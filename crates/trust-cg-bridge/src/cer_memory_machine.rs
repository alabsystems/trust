//! Actual-object memory observation hooks for PTR.3b.
//!
//! This is an auditor of individual decoded steps, not another machine executor.
//! It re-reads the bound instruction and recomputes its official effects; a
//! caller-supplied access list cannot stand in for those effects. Every memory
//! effect is retained, including reads to ZR and accesses inside the frame.
//! Nothing here classifies a frame access, supplies a validity/alias premise,
//! authenticates execution completeness, or grants a CER grade. The real CER
//! executor must still connect these hooks and its complete path traversal.
//! `PendingMachineMemory` deliberately has no complete/proved constructor.

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};

use sha2::{Digest, Sha256};
use trust_disasm::decode_aarch64;
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};
use trust_types::{Formula, Sort};

use crate::cer_memory::{self, AccessKind, PathAccess, PendingMemoryObligation, PrivateFrame};
use crate::compiled_object::{
    CompiledObject, FunctionWindow, MachineSiteKind, ObjectExpectations, ObjectLayout,
    RelocationModel, hex,
};

static NEXT_SESSION: AtomicU64 = AtomicU64::new(1);

/// Largest path condition, in compact JSON bytes, that the diagnostics publish whole. A path
/// is a tree: a step after a run of stores repeats the store chain in each byte read it
/// reassembles, and s23's (`aggregate_enum_local_is_proven`) reached megabytes per step and
/// 13.9 GB of certificates file. Every path is identified by its digest; a longer one is
/// published by digest alone.
pub const PUBLISHED_PATH_BYTES: u64 = 4096;

/// A SHA-256 sink that counts what it hashes, so a term is digested without rendering it.
struct DigestWriter {
    hasher: Sha256,
    len: u64,
}
impl std::io::Write for DigestWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.hasher.update(bytes);
        self.len += bytes.len() as u64;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// SHA-256 and length of `value`'s compact JSON (the bytes `serde_json::to_vec` renders),
/// streamed through the hasher.
fn json_digest<T: serde::Serialize>(value: &T) -> Option<(String, u64)> {
    let mut sink = DigestWriter { hasher: Sha256::new(), len: 0 };
    serde_json::to_writer(&mut sink, value).ok()?;
    Some((hex(&sink.hasher.finalize()), sink.len))
}

/// A path condition as the diagnostics publish it: its digest, and the term itself while it
/// is at most [`PUBLISHED_PATH_BYTES`]. A path that does not serialize is published whole, so
/// the report's rendering fails exactly as it did before.
fn published_path(path: &Formula) -> (Option<String>, Option<Formula>) {
    match json_digest(path) {
        Some((sha, len)) => (Some(sha), (len <= PUBLISHED_PATH_BYTES).then(|| path.clone())),
        None => (None, Some(path.clone())),
    }
}

fn check(term: &Formula, sort: Sort) -> Result<(), String> {
    let actual = trust_types::smt_logic::check_formula_sort(term).map_err(|e| format!("{e:?}"))?;
    if actual == sort { Ok(()) } else { Err(format!("expected {sort:?}, got {actual:?}")) }
}
fn memory_sort() -> Sort {
    Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)))
}

/// Independently re-read object/function identity. Construction does not certify
/// `M_cg`'s producer/source/ABI correspondence.
#[derive(Clone, Debug, serde::Serialize)]
pub struct FunctionBinding {
    pub object_sha256: String,
    pub module_sha256: String,
    pub symbol: String,
    pub section: usize,
    pub start: u64,
    pub end: u64,
    pub text_sha256: String,
}

/// A function bound internally from raw object bytes and the actual module.
/// Public mutable `FunctionWindow` fields are never accepted as authority.
pub struct BoundFunction {
    binding: FunctionBinding,
    window: FunctionWindow,
}
/// Bind the actual object/module once per CER report. Function selection still
/// uses only this privately bound layout, avoiding an object reparse per body.
pub(crate) struct BoundObject {
    layout: ObjectLayout,
    object_sha256: String,
    module_sha256: String,
}
impl BoundObject {
    pub(crate) fn bind(
        object: &[u8],
        module: &trust_ir::Module,
        relocation: RelocationModel,
    ) -> Result<Self, String> {
        let parsed = CompiledObject::parse(object).map_err(|e| e.to_string())?;
        let object_sha256 = parsed.sha256_hex();
        let expectations = ObjectExpectations::from_module(module, parsed.format, relocation)
            .map_err(|e| e.to_string())?;
        let layout = ObjectLayout::bind(parsed, &expectations).map_err(|e| e.to_string())?;
        let module_bytes = serde_json::to_vec(module).map_err(|e| e.to_string())?;
        Ok(Self { layout, object_sha256, module_sha256: hex(&Sha256::digest(module_bytes)) })
    }
    pub(crate) fn function(&self, symbol: &str) -> Result<BoundFunction, String> {
        let window = self.layout.windows.get(symbol).ok_or("bound function is absent")?.clone();
        if !window.unknown.is_empty() || !window.data_in_code.is_empty() {
            return Err(format!(
                "function has unsupported structural residue: {:?}",
                window.unknown
            ));
        }
        // Relocated addresses need the real CER placement/relocation consumer.
        // Calls may be observed as pending abstract events, never executed here.
        if window.relocations.iter().any(|r| r.role != "call" && r.role != "tail") {
            return Err(
                "memory observation requires unresolved address relocations to be consumed".into(),
            );
        }
        let binding = FunctionBinding {
            object_sha256: self.object_sha256.clone(),
            module_sha256: self.module_sha256.clone(),
            symbol: symbol.into(),
            section: window.section,
            start: window.start,
            end: window.end,
            text_sha256: window.text_sha256(),
        };
        Ok(BoundFunction { binding, window })
    }
}
impl BoundFunction {
    pub fn bind(
        object: &[u8],
        module: &trust_ir::Module,
        symbol: &str,
        relocation: RelocationModel,
    ) -> Result<Self, String> {
        BoundObject::bind(object, module, relocation)?.function(symbol)
    }

    #[must_use]
    pub fn binding(&self) -> &FunctionBinding {
        &self.binding
    }
    #[must_use]
    pub fn window(&self) -> &FunctionWindow {
        &self.window
    }

    /// Preserve the real entry parameterization verbatim (including contracted
    /// C ABI carriers). No masks, zero extension or domain premise is inferred.
    pub fn begin(&self, entry: &MachineState) -> Result<ObservationSession<'_>, String> {
        check(&entry.memory, memory_sort())?;
        check(&entry.sp, Sort::BitVec(64))?;
        let session = NEXT_SESSION
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| "observation session identity space exhausted")?;
        Ok(ObservationSession {
            session,
            function: self,
            entry: entry.clone(),
            steps: Vec::new(),
            exits: Vec::new(),
            calls: Vec::new(),
            ordinary_checked: BTreeSet::new(),
            #[cfg(feature = "frame-step-reference")]
            after_states: std::collections::BTreeMap::new(),
        })
    }

    /// CER supplies its actual window, not a separately caller-built clone of
    /// selected fields. Compare every structural field to the raw-object bind.
    pub(crate) fn begin_for_window(
        &self,
        window: &FunctionWindow,
        entry: &MachineState,
    ) -> Result<ObservationSession<'_>, String> {
        if window != &self.window {
            return Err("observer window differs from CER window".into());
        }
        self.begin(entry)
    }
}

/// The official effect's index is kept even when another effect discards its
/// result. The term is unclassified: frame accesses must not disappear here.
#[derive(Clone, Debug)]
pub struct MemoryAccess {
    pub effect_index: usize,
    pub kind: AccessKind,
    pub address: Formula,
    pub width_bytes: u32,
    pub term: PathAccess,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum Control {
    Ordinary,
    Branch,
    Conditional,
    Call,
    Return,
}

#[derive(Clone, Debug)]
pub struct ObservedStep {
    pub pc: u64,
    pub instruction: [u8; 4],
    pub path: Formula,
    pub pre_sp: Formula,
    // Actual CER state at this hook. Captured identity, never a proof grade.
    #[cfg(feature = "frame-step-reference")]
    before_state: MachineState,
    pub memory_before: Formula,
    /// The exact official memory effects only. Calls are abstract transitions
    /// owned by CER, recorded separately; they are not implemented here.
    pub memory_after: Formula,
    pub effects: Vec<Effect>,
    pub accesses: Vec<MemoryAccess>,
    pub control: Control,
}

/// A session-local opaque reference; clients cannot forge a return/call step.
/// The object identity alone is insufficient: snapshots are checked against
/// the referenced step in this particular session.
pub struct StepHandle {
    index: usize,
    session: u64,
}

#[derive(Clone, Debug)]
pub struct MemoryExit {
    pub step: usize,
    pub pc: u64,
    pub path: Formula,
    pub bytes: Formula,
    pub kind: ExitKind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum ExitKind {
    Return,
    TailReturn,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum CallKind {
    Call,
    Tail,
}
#[derive(Clone, Debug)]
pub struct CallTransition {
    pub step: usize,
    pub pc: u64,
    pub path: Formula,
    pub before: Formula,
    pub after: Formula,
    pub kind: CallKind,
}

pub struct ObservationSession<'a> {
    session: u64,
    function: &'a BoundFunction,
    entry: MachineState,
    steps: Vec<ObservedStep>,
    exits: Vec<MemoryExit>,
    calls: Vec<CallTransition>,
    ordinary_checked: BTreeSet<usize>,
    #[cfg(feature = "frame-step-reference")]
    after_states: std::collections::BTreeMap<usize, MachineState>,
}
impl ObservationSession<'_> {
    /// Hook before an actual executor step. Recompute effects from the bound
    /// bytes and actual pre-state; do not trust a supplied decoded instruction,
    /// effect subset, address, width, write list, or claimed output liveness.
    pub fn before_step(
        &mut self,
        pc: u64,
        path: &Formula,
        pre: &MachineState,
        executor_effects: &[Effect],
    ) -> Result<StepHandle, String> {
        check(path, Sort::Bool)?;
        check(&pre.memory, memory_sort())?;
        check(&pre.sp, Sort::BitVec(64))?;
        let window = &self.function.window;
        if !window.reachable.contains(&pc) || pc < window.start || (pc - window.start) % 4 != 0 {
            return Err(format!("{pc:#x} is not a bound reachable instruction"));
        }
        let offset = usize::try_from(pc - window.start).map_err(|_| "PC offset overflows")?;
        let instruction: [u8; 4] = window
            .code
            .get(offset..offset.checked_add(4).ok_or("PC end overflows")?)
            .ok_or("instruction leaves the bound extent")?
            .try_into()
            .map_err(|_| "instruction is not four bytes")?;
        let decoded = decode_aarch64(&instruction, pc).map_err(|e| format!("decode: {e:?}"))?;
        let effects =
            Aarch64Semantics.effects(pre, &decoded).map_err(|e| format!("effects: {e:?}"))?;
        if effects != executor_effects {
            return Err("executor effects differ from complete decoded instruction effects".into());
        }
        let mut accesses = Vec::new();
        let mut memory = pre.clone();
        let mut control = Control::Ordinary;
        for (effect_index, effect) in effects.iter().enumerate() {
            let access = match effect {
                Effect::MemRead { address, width_bytes } => {
                    Some((AccessKind::Read, address, *width_bytes))
                }
                Effect::MemWrite { address, width_bytes, .. } => {
                    Some((AccessKind::Write, address, *width_bytes))
                }
                Effect::Call { .. } => {
                    control = Control::Call;
                    None
                }
                Effect::Return { .. } => {
                    control = Control::Return;
                    None
                }
                Effect::Branch { .. } => {
                    control = Control::Branch;
                    None
                }
                Effect::ConditionalBranch { .. } => {
                    control = Control::Conditional;
                    None
                }
                Effect::PcUpdate { value } => {
                    if control == Control::Ordinary && matches!(value, Formula::Ite(..)) {
                        control = Control::Conditional;
                    }
                    None
                }
                Effect::RegWrite { .. }
                | Effect::SpWrite { .. }
                | Effect::FpRegWrite { .. }
                | Effect::FlagUpdate { .. } => None,
                // Fail closed on atomic, synchronization and future effects.
                other => {
                    return Err(format!("unsupported observation effect {}", other.variant_name()));
                }
            };
            if let Some((kind, address, width_bytes)) = access {
                let term = PathAccess::new(kind, path.clone(), address.clone(), width_bytes)?;
                if let Effect::MemWrite { value, .. } = effect {
                    let sort = trust_types::smt_logic::check_formula_sort(value)
                        .map_err(|e| format!("{e:?}"))?;
                    if !matches!(sort, Sort::BitVec(bits) if bits >= width_bytes * 8 && bits <= 128)
                    {
                        return Err(
                            "machine store value has insufficient or unsupported bits".into()
                        );
                    }
                    memory.apply_effect(effect).map_err(|e| format!("memory effect: {e:?}"))?;
                }
                accesses.push(MemoryAccess {
                    effect_index,
                    kind,
                    address: address.clone(),
                    width_bytes,
                    term,
                });
            }
        }
        let index = self.steps.len();
        self.steps.push(ObservedStep {
            pc,
            instruction,
            path: path.clone(),
            pre_sp: pre.sp.clone(),
            #[cfg(feature = "frame-step-reference")]
            before_state: pre.clone(),
            memory_before: pre.memory.clone(),
            memory_after: memory.memory,
            effects,
            accesses,
            control,
        });
        Ok(StepHandle { index, session: self.session })
    }

    fn step(&self, handle: &StepHandle) -> Result<&ObservedStep, String> {
        if handle.session != self.session {
            return Err("step handle belongs to a different observation session".into());
        }
        self.steps.get(handle.index).ok_or_else(|| "step handle is absent".into())
    }

    /// Hook after ordinary effects are applied. Calls use `after_call` because
    /// their real CER rely is a separately pending abstract transition.
    pub fn after_step(&mut self, handle: &StepHandle, actual: &MachineState) -> Result<(), String> {
        let step = self.step(handle)?;
        if step.control == Control::Call || actual.memory != step.memory_after {
            return Err(
                "ordinary post-state does not match the complete observed memory effects".into()
            );
        }
        if !self.ordinary_checked.insert(handle.index) {
            return Err("ordinary step was already checked".into());
        }
        #[cfg(feature = "frame-step-reference")]
        self.after_states.insert(handle.index, actual.clone());
        Ok(())
    }

    /// A real RET snapshot must agree with the exact observed memory effects.
    /// Path traversal completeness remains a separate missing CER integration.
    pub fn at_return(&mut self, handle: &StepHandle, actual: &MachineState) -> Result<(), String> {
        if self.exits.iter().any(|exit| exit.step == handle.index) {
            return Err("return step was already recorded".into());
        }
        let step = self.step(handle)?;
        if step.control != Control::Return || actual.memory != step.memory_after {
            return Err("return snapshot does not match an observed RET and its memory".into());
        }
        self.exits.push(MemoryExit {
            step: handle.index,
            pc: step.pc,
            path: step.path.clone(),
            bytes: actual.memory.clone(),
            kind: ExitKind::Return,
        });
        #[cfg(feature = "frame-step-reference")]
        self.after_states.insert(handle.index, actual.clone());
        Ok(())
    }

    /// Record CER's actual abstract call transition verbatim. It carries NO
    /// proof that pre-call equality/callee premises or the rely are justified.
    pub fn after_call(&mut self, handle: &StepHandle, actual: &MachineState) -> Result<(), String> {
        if self.calls.iter().any(|call| call.step == handle.index) {
            return Err("call transition was already recorded".into());
        }
        let step = self.step(handle)?;
        check(&actual.memory, memory_sort())?;
        if step.control != Control::Call {
            return Err("call snapshot has no observed Call".into());
        }
        self.calls.push(CallTransition {
            step: handle.index,
            pc: step.pc,
            path: step.path.clone(),
            before: step.memory_before.clone(),
            after: actual.memory.clone(),
            kind: CallKind::Call,
        });
        #[cfg(feature = "frame-step-reference")]
        self.after_states.insert(handle.index, actual.clone());
        Ok(())
    }

    /// A relocated tail branch is an abstract call followed by this function's
    /// exit. Authenticate the actual bound named Tail site; never fabricate a
    /// Call effect or a RET. Its pre-rely ordinary effects must be checked by
    /// `after_step` before invoking this hook. This remains pending evidence.
    pub fn after_tail_call(
        &mut self,
        handle: &StepHandle,
        actual: &MachineState,
    ) -> Result<(), String> {
        if self.calls.iter().any(|call| call.step == handle.index)
            || self.exits.iter().any(|exit| exit.step == handle.index)
        {
            return Err("tail transition was already recorded".into());
        }
        let step = self.step(handle)?;
        check(&actual.memory, memory_sort())?;
        let named_tail = self
            .function
            .window
            .site_at(step.pc)
            .is_some_and(|site| site.kind == MachineSiteKind::Tail && site.callee.is_some());
        if step.control != Control::Branch
            || !named_tail
            || !self.ordinary_checked.contains(&handle.index)
        {
            return Err("tail snapshot has no bound named Tail branch".into());
        }
        let pc = step.pc;
        let path = step.path.clone();
        let before = step.memory_after.clone();
        self.calls.push(CallTransition {
            step: handle.index,
            pc,
            path: path.clone(),
            before,
            after: actual.memory.clone(),
            kind: CallKind::Tail,
        });
        self.exits.push(MemoryExit {
            step: handle.index,
            pc,
            path,
            bytes: actual.memory.clone(),
            kind: ExitKind::TailReturn,
        });
        #[cfg(feature = "frame-step-reference")]
        self.after_states.insert(handle.index, actual.clone());
        Ok(())
    }

    #[must_use]
    pub fn into_pending(self) -> PendingMachineMemory {
        PendingMachineMemory {
            binding: self.function.binding.clone(),
            entry: self.entry,
            steps: self.steps,
            exits: self.exits,
            calls: self.calls,
            #[cfg(feature = "frame-step-reference")]
            after_states: self.after_states,
        }
    }
}

/// Observations are immutable and explicitly incomplete as proof evidence.
/// Even a caller that skips instructions or supplies arbitrary path/state data
/// cannot turn this into an authenticated full execution or a shipping token.
#[derive(Clone, Debug)]
pub struct PendingMachineMemory {
    binding: FunctionBinding,
    entry: MachineState,
    steps: Vec<ObservedStep>,
    exits: Vec<MemoryExit>,
    calls: Vec<CallTransition>,
    #[cfg(feature = "frame-step-reference")]
    after_states: std::collections::BTreeMap<usize, MachineState>,
}
impl PendingMachineMemory {
    #[must_use]
    pub fn binding(&self) -> &FunctionBinding {
        &self.binding
    }
    #[must_use]
    pub fn entry(&self) -> &MachineState {
        &self.entry
    }
    #[must_use]
    pub fn steps(&self) -> &[ObservedStep] {
        &self.steps
    }
    #[must_use]
    pub fn exits(&self) -> &[MemoryExit] {
        &self.exits
    }
    #[must_use]
    pub fn calls(&self) -> &[CallTransition] {
        &self.calls
    }

    /// Actual callback states for the independently checked frame composition.
    /// These snapshots supply no PC, call-rely, ABI or source-execution proof.
    #[cfg(feature = "frame-step-reference")]
    pub(crate) fn states_at(&self, index: usize) -> Result<(&MachineState, &MachineState), String> {
        let step = self.steps.get(index).ok_or("frame state step is absent")?;
        let after =
            self.after_states.get(&index).ok_or("actual frame post-state callback is absent")?;
        Ok((&step.before_state, after))
    }

    /// Diagnostic publication only. Counts and paths do not constitute a
    /// traversal seal or a machine/source correspondence certificate.
    #[must_use]
    pub fn diagnostics(&self, incomplete: Vec<String>) -> ObservationDiagnostics {
        let digest = |value: &Formula| json_digest(value).map(|(sha, _)| sha);
        ObservationDiagnostics {
            schema: "trust-cg-bridge.pending-machine-memory.v1",
            binding: Some(self.binding.clone()),
            entry_memory_sha256: digest(&self.entry.memory),
            entry_sp: Some(self.entry.sp.clone()),
            steps: self
                .steps
                .iter()
                .enumerate()
                .map(|(occurrence, step)| {
                    let (path_sha256, path) = published_path(&step.path);
                    StepDiagnostic {
                        occurrence,
                        pc: step.pc,
                        path_sha256,
                        path,
                        control: step.control,
                        reads: step.accesses.iter().filter(|a| a.kind == AccessKind::Read).count(),
                        writes: step
                            .accesses
                            .iter()
                            .filter(|a| a.kind == AccessKind::Write)
                            .count(),
                    }
                })
                .collect(),
            exits: self
                .exits
                .iter()
                .map(|exit| {
                    let (path_sha256, path) = published_path(&exit.path);
                    ExitDiagnostic {
                        occurrence: exit.step,
                        pc: exit.pc,
                        path_sha256,
                        path,
                        kind: exit.kind,
                        memory_sha256: digest(&exit.bytes),
                    }
                })
                .collect(),
            calls: self
                .calls
                .iter()
                .map(|call| {
                    let (path_sha256, path) = published_path(&call.path);
                    CallDiagnostic {
                        occurrence: call.step,
                        pc: call.pc,
                        path_sha256,
                        path,
                        kind: call.kind,
                        before_sha256: digest(&call.before),
                        after_sha256: digest(&call.after),
                    }
                })
                .collect(),
            incomplete,
            missing_integration: self.missing_integration(),
        }
    }
    #[must_use]
    pub fn missing_integration(&self) -> &'static str {
        "pending actual CER execution coverage and register/SP/flag correspondence, O5-owned validated frame partition, justified M1' separation, M3/M4/M5 discharge, complete return-path coverage and unrestricted-query O6, legal M6 witness and independent M8 kernel correspondence; Unknown"
    }

    /// Pending coverage for ALL observed accesses. Private frame accesses stay
    /// present; only the existing O5 owner may later validate their partition.
    /// An extra/dead read is inconclusive even when exit memory is unchanged.
    #[must_use]
    pub fn coverage_unclassified(&self, source: &[PathAccess]) -> Vec<PendingMemoryObligation> {
        let accesses: Vec<_> =
            self.steps.iter().flat_map(|s| s.accesses.iter().map(|a| a.term.clone())).collect();
        cer_memory::coverage(source, &accesses)
    }

    /// Diagnostic term construction over recorded exits, not a source-bound
    /// completeness theorem. `query` is checked fresh by the shared builder.
    pub fn exit_memory_obligations(
        &self,
        source_path: &Formula,
        source_memory: &Formula,
        query: &Formula,
        frame: &PrivateFrame,
    ) -> Result<Vec<PendingMemoryObligation>, String> {
        if self.exits.is_empty() {
            return Err("no observed return: execution coverage is incomplete".into());
        }
        self.exits
            .iter()
            .map(|exit| {
                let reach = Formula::And(vec![source_path.clone(), exit.path.clone()]);
                cer_memory::outside_memory_equal(&reach, source_memory, &exit.bytes, query, frame)
            })
            .collect()
    }
}

/// Non-authoritative diagnostics attached to the existing function report.
/// There is deliberately no complete/proved flag or conversion into a grade.
#[derive(Clone, Debug, serde::Serialize)]
pub struct ObservationDiagnostics {
    pub schema: &'static str,
    pub binding: Option<FunctionBinding>,
    pub entry_memory_sha256: Option<String>,
    pub entry_sp: Option<Formula>,
    pub steps: Vec<StepDiagnostic>,
    pub exits: Vec<ExitDiagnostic>,
    pub calls: Vec<CallDiagnostic>,
    pub incomplete: Vec<String>,
    pub missing_integration: &'static str,
}
impl ObservationDiagnostics {
    pub(crate) fn unavailable(incomplete: Vec<String>) -> Self {
        Self {
            schema: "trust-cg-bridge.pending-machine-memory.v1",
            binding: None,
            entry_memory_sha256: None,
            entry_sp: None,
            steps: Vec::new(),
            exits: Vec::new(),
            calls: Vec::new(),
            incomplete,
            missing_integration: "pending actual observation, full path and state correspondence, M1/M3/O6/M5/M6/M8; Unknown",
        }
    }
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct StepDiagnostic {
    pub occurrence: usize,
    pub pc: u64,
    /// SHA-256 of the path condition's compact JSON.
    pub path_sha256: Option<String>,
    /// The path condition, while it is at most [`PUBLISHED_PATH_BYTES`] of compact JSON.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<Formula>,
    pub control: Control,
    pub reads: usize,
    pub writes: usize,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct ExitDiagnostic {
    pub occurrence: usize,
    pub pc: u64,
    /// SHA-256 of the path condition's compact JSON.
    pub path_sha256: Option<String>,
    /// The path condition, while it is at most [`PUBLISHED_PATH_BYTES`] of compact JSON.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<Formula>,
    pub kind: ExitKind,
    pub memory_sha256: Option<String>,
}
#[derive(Clone, Debug, serde::Serialize)]
pub struct CallDiagnostic {
    pub occurrence: usize,
    pub pc: u64,
    /// SHA-256 of the path condition's compact JSON.
    pub path_sha256: Option<String>,
    /// The path condition, while it is at most [`PUBLISHED_PATH_BYTES`] of compact JSON.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<Formula>,
    pub kind: CallKind,
    pub before_sha256: Option<String>,
    pub after_sha256: Option<String>,
}

#[cfg(test)]
#[path = "cer_memory_machine/tests.rs"]
mod tests;
