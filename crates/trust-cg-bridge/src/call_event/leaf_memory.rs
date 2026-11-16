//! Authenticated inputs for the bounded frameless, call-free memory leaf proof.
//!
//! This module seals the actual linear source/executor census and consumes all
//! original ABI/scalar/coverage/entire-memory equations as ONE Clean kernel goal.
//! Only its private Closed receipt authorizes the bounded leaf admission. Every
//! missing witness or kernel decline retains Unknown; total byte arrays add no
//! pointer validity, private-frame separation or noalias premise.

use super::*;
use crate::cer_memory::{AccessKind, PathAccess};
use crate::cer_memory_machine::{BoundFunction, FunctionBinding};

fn same_state(a: &MachineState, c: &MachineState) -> bool {
    a.gpr == c.gpr
        && a.fpr == c.fpr
        && a.sp == c.sp
        && a.pc == c.pc
        && a.memory == c.memory
        && a.flags.n == c.flags.n
        && a.flags.z == c.flags.z
        && a.flags.c == c.flags.c
        && a.flags.v == c.flags.v
}
fn byte_address(address: &Formula, offset: u32) -> Formula {
    if offset == 0 {
        address.clone()
    } else {
        Formula::BvAdd(
            b(address.clone()),
            b(Formula::BitVec { value: i128::from(offset), width: 64 }),
            64,
        )
    }
}
fn mentions_variable(formula: &Formula, name: &str) -> bool {
    let mut found = false;
    formula.visit(&mut |term| {
        if matches!(term, Formula::Var(n, _) if n == name)
            || matches!(term, Formula::SymVar(n, _) if n.as_str() == name)
        {
            found = true;
        }
    });
    found
}

/// Object-section PCs authenticate traversal, but are not loaded addresses.
/// Until placement is bound, a decoder-resolved data address cannot be used as
/// a machine value. Control targets are independently excluded by this trace.
fn unplaced_pc_data(instruction: &trust_disasm::Instruction) -> bool {
    crate::pc_object_model::requires_runtime_placement(instruction)
}

/// No public completion bit or PC-set constructor exists. Every successor is
/// exactly the next four bound bytes, and every actual state transition is
/// compared with applying the complete official ordinary effects.
pub(super) struct Trace {
    binding: FunctionBinding,
    window: FunctionWindow,
    entry: MachineState,
    expected: MachineState,
    next: u64,
    in_flight: Option<(u64, bool)>,
    returned: bool,
    accesses: Vec<PathAccess>,
    instructions: usize,
    refusal: Option<String>,
    return_target: Option<Formula>,
    x18_written: bool,
    // Actual pre-states, retained only by the authenticated ordinary trace.
    prefixes: Vec<(u64, MachineState)>,
}
impl Trace {
    pub fn begin(
        function: &BoundFunction,
        window: &FunctionWindow,
        entry: &MachineState,
    ) -> Result<Self, String> {
        if function.window() != window || !window.sites.is_empty() || !window.relocations.is_empty()
        {
            return Err(
                "leaf requires the exact bound window and no calls/address relocations".into()
            );
        }
        Ok(Self {
            binding: function.binding().clone(),
            window: window.clone(),
            entry: entry.clone(),
            expected: entry.clone(),
            next: window.start,
            in_flight: None,
            returned: false,
            accesses: Vec::new(),
            instructions: 0,
            refusal: None,
            return_target: None,
            x18_written: false,
            prefixes: Vec::new(),
        })
    }
    pub fn reject(&mut self, reason: String) {
        self.refusal.get_or_insert(reason);
    }
    pub fn before(
        &mut self,
        pc: u64,
        path: &Formula,
        pre: &MachineState,
        effects: &[Effect],
    ) -> Result<(), String> {
        let result = self.before_inner(pc, path, pre, effects);
        if let Err(reason) = &result {
            self.reject(reason.clone());
        }
        result
    }
    fn before_inner(
        &mut self,
        pc: u64,
        path: &Formula,
        pre: &MachineState,
        effects: &[Effect],
    ) -> Result<(), String> {
        if self.refusal.is_some()
            || self.returned
            || self.in_flight.is_some()
            || pc != self.next
            || *path != Formula::Bool(true)
            || !same_state(pre, &self.expected)
        {
            return Err("leaf traversal/state continuity is incomplete or non-linear".into());
        }
        let i =
            usize::try_from(pc.checked_sub(self.window.start).ok_or("leaf PC precedes extent")?)
                .map_err(|_| "leaf PC overflows")?;
        let bytes = self
            .window
            .code
            .get(i..i.checked_add(4).ok_or("leaf PC end overflows")?)
            .ok_or("leaf instruction leaves actual extent")?;
        let decoded = decode_aarch64(bytes, pc).map_err(|e| format!("leaf decode: {e:?}"))?;
        if unplaced_pc_data(&decoded) {
            return Err("leaf PC-relative data has no authenticated loaded placement".into());
        }
        let official =
            Aarch64Semantics.effects(pre, &decoded).map_err(|e| format!("leaf effects: {e:?}"))?;
        if official != effects {
            return Err("leaf actual effects differ from the bound decoder".into());
        }
        let mut post = pre.clone();
        let mut returning = false;
        let return_target = effects.iter().find_map(|effect| match effect {
            Effect::Return { target } => Some(target),
            _ => None,
        });
        let advance =
            Formula::BvAdd(b(pre.pc.clone()), b(Formula::BitVec { value: 4, width: 64 }), 64);
        for effect in effects {
            if matches!(effect, Effect::RegWrite { index: 18, .. }) {
                self.x18_written = true;
            }
            match effect {
                Effect::Return { .. } if decoded.opcode == Opcode::Ret && !returning => {
                    returning = true
                }
                Effect::PcUpdate { value } if *value == advance => {}
                Effect::PcUpdate { value }
                    if decoded.opcode == Opcode::Ret && return_target == Some(value) => {}
                Effect::MemRead { address, width_bytes }
                | Effect::MemWrite { address, width_bytes, .. } => {
                    if mentions_sp(address) {
                        return Err("leaf has an SP-relative/private memory access".into());
                    }
                    let kind = if matches!(effect, Effect::MemWrite { .. }) {
                        AccessKind::Write
                    } else {
                        AccessKind::Read
                    };
                    self.accesses.push(PathAccess::new(
                        kind,
                        path.clone(),
                        address.clone(),
                        *width_bytes,
                    )?);
                    post.apply_effect(effect)
                        .map_err(|e| format!("leaf memory transition: {e:?}"))?;
                }
                Effect::RegWrite { value, .. } if mentions_sp(value) => {
                    return Err("leaf materializes an SP-derived scalar".into());
                }
                Effect::RegWrite { .. } | Effect::FlagUpdate { .. } => {
                    post.apply_effect(effect)
                        .map_err(|e| format!("leaf scalar transition: {e:?}"))?;
                }
                // In particular no SpWrite, call, branch, tail, atomics, sync,
                // floating transport or unrecognized future effect is admitted.
                _ => return Err(format!("leaf unsupported effect {}", effect.variant_name())),
            }
        }
        if returning && decoded.opcode != Opcode::Ret {
            return Err("leaf fabricated return".into());
        }
        if returning {
            self.return_target = return_target.cloned();
            if !crate::compiled_object::all_padding(&self.window.code[i + 4..]) {
                return Err("leaf RET has non-padding unvisited bytes".into());
            }
        } else if decoded.opcode == Opcode::Ret {
            return Err("leaf RET has no Return effect".into());
        }
        if self.prefixes.len() < 12 {
            self.prefixes.push((pc, pre.clone()));
        }
        self.expected = post;
        self.in_flight = Some((pc, returning));
        Ok(())
    }
    pub fn after(&mut self, state: &MachineState) -> Result<(), String> {
        let result = self.after_inner(state);
        if let Err(reason) = &result {
            self.reject(reason.clone());
        }
        result
    }
    fn after_inner(&mut self, state: &MachineState) -> Result<(), String> {
        let (pc, returning) =
            self.in_flight.take().ok_or("leaf post-state has no actual pre-step")?;
        if !same_state(state, &self.expected) {
            return Err("leaf real post-state differs from official full effects".into());
        }
        self.instructions += 1;
        self.returned = returning;
        self.next = pc.checked_add(4).ok_or("leaf successor overflows")?;
        Ok(())
    }
    pub fn finish(self) -> Result<Execution, String> {
        if let Some(reason) = self.refusal {
            return Err(reason);
        }
        if !self.returned || self.in_flight.is_some() || self.instructions == 0 {
            return Err("leaf has no complete straight-line RET traversal".into());
        }
        // No SP write or SP-relative access can pass before(), and every state
        // transition was checked, so this is an empty frame derived from bytes.
        if self.entry.sp != self.expected.sp {
            return Err("leaf SP changed".into());
        }
        Ok(Execution {
            binding: self.binding,
            entry: self.entry,
            exit: self.expected,
            accesses: self.accesses,
            instructions: self.instructions,
            return_target: self.return_target.ok_or("leaf return target absent")?,
            x18_written: self.x18_written,
            prefixes: self.prefixes,
        })
    }
}
/// Sealed by Trace::finish; no caller-authored access census is accepted.
#[derive(Clone)]
pub(super) struct Execution {
    binding: FunctionBinding,
    entry: MachineState,
    exit: MachineState,
    accesses: Vec<PathAccess>,
    instructions: usize,
    return_target: Formula,
    x18_written: bool,
    prefixes: Vec<(u64, MachineState)>,
}
impl Execution {
    pub(super) fn unwind_prefixes(
        &self,
    ) -> Result<(&FunctionBinding, &MachineState, &[(u64, MachineState)]), String> {
        if self.prefixes.len() != self.instructions || self.prefixes.len() > 11 {
            return Err("compact unwind retained prefix population exceeds its bound".into());
        }
        Ok((&self.binding, &self.entry, &self.prefixes))
    }
}

/// A compound prefix+callee transition has NO ordinary call-free metadata
/// capability. In particular it cannot be passed to Execution::unwind_prefixes
/// or any consumer requiring an ordinary Trace::finish receipt. No Deref,
/// conversion back to Execution, deserialization or public constructor exists.
pub(super) struct TailExecution {
    math: KernelExecution,
}

/// Only original joint mathematical equations consume this private adapter.
/// It deliberately carries no ordinary prefix/metadata authority or constructor.
struct KernelExecution {
    binding: FunctionBinding,
    entry: MachineState,
    exit: MachineState,
    accesses: Vec<PathAccess>,
    instructions: usize,
    return_target: Formula,
    x18_written: bool,
}
impl KernelExecution {
    fn from_leaf(execution: Execution) -> Self {
        Self {
            binding: execution.binding,
            entry: execution.entry,
            exit: execution.exit,
            accesses: execution.accesses,
            instructions: execution.instructions,
            return_target: execution.return_target,
            x18_written: execution.x18_written,
        }
    }
}

/// Replay must decline calls/control before event pairing could invoke a solver.
/// This is a necessary syntactic restriction, not a source-completeness proof;
/// Source::read and the sealed trace still check every semantic requirement.
pub(super) fn replay_source_shape(function: &trust_ir::Function) -> Result<(), String> {
    let refuse = || {
        "retained original replay supports one unconditional call-free returning block".to_string()
    };
    if function.blocks.len() != 1 || function.blocks[0].id != function.entry {
        return Err(refuse());
    }
    let body = &function.blocks[0].body;
    if !matches!(body.last().map(|node| &node.inst), Some(Inst::Return { .. })) {
        return Err(refuse());
    }
    for (index, node) in body.iter().enumerate() {
        match &node.inst {
            Inst::Load { volatile: false, .. }
            | Inst::Store { volatile: false, .. }
            | Inst::Const { .. }
            | Inst::Copy { .. }
            | Inst::Cast { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::GEP { .. }
            // This is only the replay shape prefilter. Source::read below
            // checks the full nominal declaration/layout and exact field.
            | Inst::ExtractField { .. } => {}
            Inst::Return { .. } if index + 1 == body.len() => {}
            _ => return Err(refuse()),
        }
    }
    Ok(())
}

pub(super) struct Source {
    entry: Formula,
    exit: Formula,
    accesses: Vec<PathAccess>,
    value: Formula,
}
impl Source {
    pub fn read(
        module: &Module,
        function: &trust_ir::Function,
        spec: &SpecResult,
        codegen: &Module,
        symbol: &str,
    ) -> Result<Self, String> {
        let sig = module.func_type(function.ty).ok_or("leaf source signature missing")?;
        let actual = codegen
            .functions
            .iter()
            .find(|function| function.name == symbol)
            .ok_or("leaf codegen function is absent")?;
        let actual_sig = codegen.func_type(actual.ty).ok_or("leaf codegen signature absent")?;
        if function.blocks.len() != 1
            || function.blocks[0].id != function.entry
            || sig.is_vararg
            || sig.abi.is_some()
            || !abi_extensions::qualified_target(module)
            || !matches!(function.calling_conv, CallingConv::C | CallingConv::Rust)
            || !abi_extensions::qualified_target(codegen)
            || actual.calling_conv != function.calling_conv
            || actual_sig.is_vararg
            || actual_sig.abi.is_some()
            || actual_sig.params != sig.params
            || actual_sig.returns != sig.returns
            || sig.returns.iter().any(|ty| source_memory::width(ty).is_err())
            || spec.reach != Formula::Bool(true)
            || !spec.side.is_empty()
            || !spec.events.is_empty()
            || !spec.result_vars.is_empty()
            || !spec.memory.calls.is_empty()
            || spec.memory.exits.len() != 1
            || spec.memory.exits[0].path != Formula::Bool(true)
        {
            return Err(
                "leaf source is not one unconditional scalar call-free returning block".into()
            );
        }
        for ty in &sig.params {
            match ty {
                IrTy::Closure(nominal) => {
                    closure_values::original_nominal(module, codegen, *nominal)?
                }
                _ => {
                    source_memory::width(ty)?;
                }
            }
        }
        let block = &function.blocks[0];
        let mut census = Vec::new();
        for (index, node) in block.body.iter().enumerate() {
            match &node.inst {
                Inst::Load { ty, volatile: false, .. } => census.push((
                    (block.id.index(), index),
                    AccessKind::Read,
                    source_memory::width(ty)?,
                )),
                Inst::Store { ty, volatile: false, .. } => census.push((
                    (block.id.index(), index),
                    AccessKind::Write,
                    source_memory::width(ty)?,
                )),
                Inst::Const { .. }
                | Inst::Copy { .. }
                | Inst::Cast { .. }
                | Inst::BinOp { .. }
                | Inst::UnOp { .. }
                | Inst::GEP { .. } => {}
                Inst::ExtractField { ty, aggregate, field } if node.results.len() == 1 => {
                    closure_values::original_projection(
                        module, function, codegen, *aggregate, *field, ty,
                    )?;
                }
                Inst::Return { .. } if index + 1 == block.body.len() => {}
                _ => {
                    return Err(
                        "leaf source contains control/volatile/unsupported instruction".into()
                    );
                }
            }
        }
        if !matches!(block.body.last().map(|n| &n.inst), Some(Inst::Return { .. }))
            || census.len() != spec.memory.accesses.len()
        {
            return Err("leaf source memory/return census is incomplete".into());
        }
        for ((site, kind, width), access) in census.iter().zip(&spec.memory.accesses) {
            if *site != access.site
                || *kind != access.term.kind()
                || *width != access.term.width_bytes()
                || *access.term.reach() != Formula::Bool(true)
                || access.origin.projection.is_some()
                || access.origin.argument as usize >= block.params.len()
            {
                return Err("leaf source typed access census differs from evaluated paths".into());
            }
        }
        Ok(Self {
            entry: spec.memory.entry.clone(),
            exit: spec.memory.exits[0].bytes.clone(),
            accesses: spec.memory.accesses.iter().map(|a| a.term.clone()).collect(),
            value: spec.value.clone(),
        })
    }
}

impl Source {
    /// Only a sealed complete source-call/return + empty-prefix witness can
    /// instantiate this already authenticated actual source leaf transition.
    pub(super) fn at_empty_tail(
        self,
        tail: &leaf_call_instance::TailContext,
    ) -> Result<Self, String> {
        let entry = tail.instantiate(&self.entry)?;
        if entry != tail.entry().memory || tail.tail_entry().memory != entry {
            return Err("tail source call and machine prefix do not share exact M0".into());
        }
        let accesses = self
            .accesses
            .iter()
            .map(|access| {
                PathAccess::new(
                    access.kind(),
                    tail.instantiate(access.reach())?,
                    tail.instantiate(access.address())?,
                    access.width_bytes(),
                )
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(Self {
            entry,
            exit: tail.instantiate(&self.exit)?,
            accesses,
            value: tail.instantiate(&self.value)?,
        })
    }
}
impl Execution {
    /// Compose two sealed actual traversals. The prefix has no memory/SP/X18/
    /// LR/frame writes or unobserved instructions; this leaf execution starts
    /// at its EXACT complete post-state and reaches a real RET. No rely array
    /// or synthetically authored machine outcome supplies these transitions.
    pub(super) fn at_empty_tail(
        self,
        tail: &leaf_call_instance::TailContext,
        caller: &BoundFunction,
    ) -> Result<TailExecution, String> {
        if !same_state(&self.entry, tail.tail_entry())
            || self.binding.symbol != tail.callee_symbol()
            || caller.binding().symbol != tail.caller_symbol()
            || self.binding.object_sha256 != caller.binding().object_sha256
            || self.binding.module_sha256 != caller.binding().module_sha256
            || self.entry.memory != tail.entry().memory
            || self.entry.sp != tail.entry().sp
        {
            return Err(
                "tail/callee/caller execution identities or full boundary state differ".into()
            );
        }
        let mut math = KernelExecution::from_leaf(self);
        math.binding = caller.binding().clone();
        math.entry = tail.entry().clone();
        math.instructions = math
            .instructions
            .checked_add(tail.prefix_instructions())
            .ok_or("tail instruction census overflow")?;
        Ok(TailExecution { math })
    }
}

/// Actual original-formula obligations for the future SAME kernel conjunction.
/// No solver-only result or this object can grant a shipping grade.
pub(super) struct KernelInputs {
    equations: Vec<(Formula, Formula)>,
    diagnostic: Diagnostic,
    source_value: Formula,
    entry: MachineState,
    exit: MachineState,
    return_target: Formula,
    x18_written: bool,
    query_name: String,
    memory_equation: usize,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct Diagnostic {
    pub status: String,
    pub instructions: usize,
    pub source_accesses: usize,
    pub machine_accesses: usize,
    pub source_coverage_bytes: usize,
    pub query: String,
    pub private_frame_bytes: Option<u64>,
    pub original_joint_equations: Option<usize>,
}
impl Diagnostic {
    pub(super) fn refused(reason: String) -> Self {
        Self {
            status: format!("leaf evidence unavailable: {reason}; Unknown"),
            instructions: 0,
            source_accesses: 0,
            machine_accesses: 0,
            source_coverage_bytes: 0,
            query: String::new(),
            private_frame_bytes: None,
            original_joint_equations: None,
        }
    }
}
impl KernelInputs {
    pub(super) fn original_equations(&self) -> &[(Formula, Formula)] {
        &self.equations
    }
    pub(super) fn diagnostic(&self) -> &Diagnostic {
        &self.diagnostic
    }
    pub fn derive(source: Source, execution: Execution) -> Result<Self, String> {
        Self::derive_inner(source, KernelExecution::from_leaf(execution), None, false)
    }
    pub(super) fn derive_replay(
        source: Source,
        execution: Execution,
        packet: &crate::original_conjunction_certificate::OriginalConjunctionCertificate,
    ) -> Result<Self, String> {
        Self::derive_inner(
            source,
            KernelExecution::from_leaf(execution),
            Some(packet.original_equations()),
            false,
        )
    }
    pub(super) fn derive_tail_original(
        source: Source,
        execution: TailExecution,
        retained_original: &[(Formula, Formula)],
    ) -> Result<Self, String> {
        Self::derive_inner(source, execution.math, Some(retained_original), true)
    }
    fn derive_inner(
        source: Source,
        execution: KernelExecution,
        retained: Option<&[(Formula, Formula)]>,
        same_kind: bool,
    ) -> Result<Self, String> {
        if source.entry != execution.entry.memory {
            return Err("leaf source/machine initial arrays differ".into());
        }
        let query_name = format!(
            "CER_LEAF_QUERY@{}:{}",
            execution.binding.object_sha256, execution.binding.symbol
        );
        let query = Formula::Var(query_name.clone(), Sort::BitVec(64));
        for formula in [
            &source.entry,
            &source.exit,
            &source.value,
            &execution.entry.sp,
            &execution.entry.pc,
            &execution.entry.flags.n,
            &execution.entry.flags.z,
            &execution.entry.flags.c,
            &execution.entry.flags.v,
            &execution.exit.memory,
        ]
        .into_iter()
        .chain(execution.entry.gpr.iter())
        .chain(execution.entry.fpr.iter())
        .chain(source.accesses.iter().map(|a| a.address()))
        .chain(execution.accesses.iter().map(|a| a.address()))
        {
            if mentions_variable(formula, &query_name) {
                return Err("leaf query is contaminated by modeled inputs".into());
            }
        }
        let mut equations = Vec::new();
        for machine in &execution.accesses {
            for byte in 0..machine.width_bytes() {
                let address = byte_address(machine.address(), byte);
                // A retained RHS is an untrusted finite witness selection, not
                // equality authority. Rebuild its allowed source-kind/address
                // census without a solver, then check the actual equality in
                // the SAME complete original retained kernel goal below.
                let claimed = match retained {
                    Some(pairs) => {
                        let (left, right) = pairs
                            .get(equations.len())
                            .ok_or("retained leaf coverage witness is absent")?;
                        if *left != address {
                            return Err(
                                "retained leaf witness changes actual machine byte address".into(),
                            );
                        }
                        Some(right)
                    }
                    None => None,
                };
                let mut witness = None;
                'search: for original in &source.accesses {
                    if (same_kind && machine.kind() != original.kind())
                        || (machine.kind() == AccessKind::Write
                            && original.kind() != AccessKind::Write)
                    {
                        continue;
                    }
                    for offset in 0..original.width_bytes() {
                        let candidate = byte_address(original.address(), offset);
                        let selected = match claimed {
                            Some(right) => *right == candidate,
                            None => matches!(
                                discharge_equal_pre(&address, &candidate, None),
                                Discharge::Proven
                            ),
                        };
                        if selected {
                            witness = Some(candidate);
                            break 'search;
                        }
                    }
                }
                let witness =
                    witness.ok_or("leaf has a machine byte without source coverage; Unknown")?;
                // Producer AY or untrusted retained data only chooses a finite
                // witness. This ORIGINAL equality is checked in the joint goal.
                equations.push((address, witness));
            }
        }
        let bytes = equations.len();
        equations.push((
            Formula::Select(b(execution.exit.memory.clone()), b(query.clone())),
            Formula::Select(b(source.exit), b(query)),
        ));
        Ok(Self { equations, source_value: source.value,
            entry: execution.entry, exit: execution.exit,
            return_target: execution.return_target, x18_written: execution.x18_written,
            query_name: query_name.clone(), memory_equation: bytes,
            diagnostic: Diagnostic { status: "authenticated straight-line source/execution inputs; original scalar+memory joint kernel pending; Unknown".into(),
            instructions: execution.instructions, source_accesses: source.accesses.len(),
            machine_accesses: execution.accesses.len(), source_coverage_bytes: bytes,
            query: query_name, private_frame_bytes: Some(0), original_joint_equations: None } })
    }

    /// Consume every original obligation in one checked goal. No solver verdict,
    /// per-item grade composition, abi_fold or dummy/normalized memory is used.
    fn prepare_original(
        mut self,
        place: &FnPlacement,
        entry_abi: &abi_extensions::Plan,
        actual_outcome: &PathOutcome,
        x18_reserved: bool,
    ) -> Result<ExpectedOriginal, String> {
        if !x18_reserved || self.x18_written {
            return Err("leaf requires the actual Darwin reserved-X18 guarantee".into());
        }
        let machine_value = match &place.ret {
            ReturnPlace::Void => Formula::BitVec { value: 0, width: 1 },
            ReturnPlace::Scalar(s) if s.slot == Slot::Gpr(0) && s.width <= 64 => {
                self.exit.read_gpr(0, abi_extensions::physical_width(s))
            }
            _ => return Err("leaf physical return transport is unsupported".into()),
        };
        if actual_outcome.reach != Formula::Bool(true)
            || actual_outcome.value != machine_value
            || actual_outcome.abi != AbiExit::at(&self.exit, self.return_target.clone())
            || actual_outcome.x18_written != Formula::Bool(self.x18_written)
            || !actual_outcome.arrivals.is_empty()
        {
            return Err("leaf sealed exit differs from the actual CER outcome".into());
        }
        // ALL original O0 locations, including exact identities. Never use the
        // abi_fold-normalized residue as the statement of this new proof.
        for register in 19..=29 {
            self.equations
                .push((self.exit.read_gpr(register, 64), self.entry.read_gpr(register, 64)));
        }
        self.equations.push((self.exit.sp.clone(), self.entry.sp.clone()));
        for register in 8..=15 {
            self.equations
                .push((self.exit.read_fpr(register, 64), self.entry.read_fpr(register, 64)));
        }
        self.equations.push((self.return_target, self.entry.read_gpr(30, 64)));
        let source_value = match &place.ret {
            ReturnPlace::Void => self.source_value,
            ReturnPlace::Scalar(s) => abi_extensions::physical_value(s, self.source_value)?,
            _ => return Err("leaf source return transport is unsupported".into()),
        };
        self.equations.push((machine_value, source_value));
        self.equations.extend(entry_abi.entry_equations());
        // Keep the query independent of the COMPLETE original goal, including
        // scalar/ABI/entry laws added after the memory witness was derived.
        let query = Formula::Var(self.query_name.clone(), Sort::BitVec(64));
        for (index, (left, right)) in self.equations.iter().enumerate() {
            if index == self.memory_equation {
                match (left, right) {
                    (Formula::Select(lm, lq), Formula::Select(rm, rq))
                        if **lq == query
                            && **rq == query
                            && !mentions_variable(lm, &self.query_name)
                            && !mentions_variable(rm, &self.query_name) => {}
                    _ => {
                        return Err(
                            "leaf whole-array equation lost its fresh unrestricted query".into()
                        );
                    }
                }
            } else if mentions_variable(left, &self.query_name)
                || mentions_variable(right, &self.query_name)
            {
                return Err("leaf query contaminated the original scalar/ABI/coverage goal".into());
            }
        }
        Ok(ExpectedOriginal { equations: self.equations, diagnostic: self.diagnostic })
    }
    pub(super) fn expected_tail(
        self,
        place: &FnPlacement,
        entry_abi: &abi_extensions::Plan,
        actual_outcome: &PathOutcome,
        bindings: &[(Formula, Formula)],
    ) -> Result<ExpectedOriginal, String> {
        let mut expected = self.prepare_original(place, entry_abi, actual_outcome, true)?;
        if bindings.iter().any(|(a, c)| a != c) {
            return Err("tail original physical argument binding differs".into());
        }
        let mut whole = bindings.to_vec();
        whole.extend(expected.equations);
        expected.equations = whole;
        Ok(expected)
    }
    pub(super) fn close(
        self,
        place: &FnPlacement,
        entry_abi: &abi_extensions::Plan,
        actual_outcome: &PathOutcome,
        x18_reserved: bool,
        retained: Option<&crate::original_conjunction_certificate::OriginalConjunctionCertificate>,
    ) -> Result<Closed, String> {
        let expected = self.prepare_original(place, entry_abi, actual_outcome, x18_reserved)?;
        let evidence: ProvenEvidence = {
            #[cfg(feature = "kernel-recheck")]
            {
                match retained {
                    Some(packet)=>{
                        let checked=packet.replay(&expected.equations)?;
                        ProvenEvidence::KernelInstantiated{theorem:checked.label().into(),original:Some(Arc::new(checked))}
                    }
                    None=>crate::verify_output::try_kernel_recheckable_original_conjunction(&expected.equations)
                        .ok_or("leaf original scalar/ABI/coverage/exit-memory joint kernel declined; Unknown")?,
                }
            }
            #[cfg(not(feature = "kernel-recheck"))]
            {
                return Err("leaf requires the actual kernel-recheck feature; Unknown".into());
            }
        };
        expected.finish(evidence)
    }
}

/// Complete independently reconstructed ORIGINAL source/machine theorem. This
/// is not checked evidence. Only finish with an exactly matching actual checked
/// packet can create Closed, and every original equation remains in the goal.
pub(super) struct ExpectedOriginal {
    equations: Vec<(Formula, Formula)>,
    diagnostic: Diagnostic,
}
impl ExpectedOriginal {
    pub(super) fn equations(&self) -> &[(Formula, Formula)] {
        &self.equations
    }
    pub(super) fn finish(mut self, evidence: ProvenEvidence) -> Result<Closed, String> {
        let ProvenEvidence::KernelInstantiated { original: Some(checked), .. } = &evidence else {
            return Err("original transition has no retained kernel-instantiated proof".into());
        };
        if checked.original_equations() != self.equations {
            return Err("checked original packet differs from complete expected transition".into());
        }
        self.diagnostic.status =
            "one original scalar/ABI/source-byte/entire-memory conjunction checked by Clean kernel"
                .into();
        self.diagnostic.original_joint_equations = Some(self.equations.len());
        Ok(Closed { evidence, diagnostic: self.diagnostic })
    }
}

/// Constructed only by consuming the sealed source/execution inputs and the
/// actual original-statement kernel result. Diagnostics cannot mint this token.
#[derive(Clone)]
pub(super) struct Closed {
    evidence: ProvenEvidence,
    diagnostic: Diagnostic,
}
impl Closed {
    pub(super) fn checked_original(
        &self,
    ) -> Option<std::sync::Arc<crate::original_conjunction_certificate::CheckedOriginalConjunction>>
    {
        match &self.evidence {
            ProvenEvidence::KernelInstantiated { original: Some(checked), .. } => {
                Some(checked.clone())
            }
            _ => None,
        }
    }
    pub(super) fn diagnostic(&self) -> &Diagnostic {
        &self.diagnostic
    }
    pub(super) fn into_evidence(self) -> ProvenEvidence {
        self.evidence
    }
}

#[cfg(test)]
#[path = "leaf_memory/tests.rs"]
mod tests;
