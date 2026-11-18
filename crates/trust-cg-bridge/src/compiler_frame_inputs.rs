//! Actual AOT frame inputs, bound to the same object and P as CER.
//!
//! This is the request side of the SemR allocation embedding. In particular,
//! matching an emitted frame envelope cannot create an entry heap or prove
//! that a raw argument avoids saved FP/LR. No constructor here creates a proof,
//! changes an obligation grade, or replaces the original unrestricted array
//! equation with an outside-frame observation.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use trust_cg_codegen::aot_frame_inputs::{AotFrameLayoutObservation, AotSourceAllocationRequest};
use trust_cg_ir::regs::{X29, X30};
use trust_types::Formula;

use crate::call_event::{
    CerInput, CerReport, FunctionCertificate, Grade, ObligationGrade, Unclosed,
};
use crate::compiled_object::{
    CompiledObject, FunctionWindow, MachineSiteKind, ObjectExpectations, ObjectLayout,
};
use crate::object_replay::artifact_digest;
use crate::verify_output::{EmitPolicy, OutputVerdict};

/// Obligations the frame observation cannot discharge. These are required
/// together, not independent alternatives or a list of permitted assumptions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum FrameInputObligation {
    /// The actual entry source allocations/bytes inject into machine memory.
    SemRAllocationEmbedding,
    /// Actual ABI pointers have their source allocation identity and offset.
    SourceArgumentPointerImages,
    /// Actual SP is the nonwrapping, aligned end of the fresh owned frame.
    ActualSpFramePlacement,
    /// Every executed instruction refines the allocation-aware memory step.
    CompleteInstructionMemoryRefinement,
    /// The exact callee preserves frame ownership and satisfies its memory rely.
    CallFrameOwnershipAndMemoryRely,
    /// Saved state and the actual return target survive arbitrary legal aliasing.
    SavedRegistersAndReturnTarget,
    /// Keep the existing full-q64 original memory goal; no outside-frame rewrite.
    OriginalUnrestrictedArrayEquation,
}

#[derive(Clone, Debug, Serialize)]
pub enum FrameEnvelopeInput {
    /// Only the byte/producer envelope matched; none of the obligations below did.
    ObservedFpLr16DirectCall { call_pc: u64, callee: String },
    /// The current reader has no complete instruction relation for this frame.
    Unsupported { reason: String },
    /// No retained producer layout exists. This never means a zero-byte frame.
    MissingProducerLayout,
}

/// A bound, explicitly pending request for the published SemR frame theorem.
/// It is diagnostic/input data only, including after successful serialization.
#[derive(Clone, Debug, Serialize)]
pub struct PendingFrameInput {
    pub schema: &'static str,
    pub symbol: String,
    pub object_sha256: String,
    pub text_sha256: String,
    pub placement_sha256: String,
    pub producer_ir_sha256: String,
    pub producer_frame_bytes: Option<u32>,
    pub producer_slot_count: usize,
    pub producer_layout: Option<ProducerFrameLayout>,
    pub producer_slots: Vec<trust_cg_ir::function::StackSlot>,
    /// Static source-site/SSA-to-slot DATA, rebound to this exact object,
    /// complete producer layout and original compiler input. A rewritten
    /// adapter input which is not retained remains an explicit error here.
    /// These records grant no runtime allocation identity or memory proof.
    pub source_stack_allocations:
        Result<trust_cg_lower::source_stack_allocations::SourceStackAllocations, String>,
    pub entry_sp: Option<Formula>,
    pub entry_memory_sha256: Option<String>,
    pub envelope: FrameEnvelopeInput,
    /// Recomputed official memory effects observed during the actual CER run.
    /// Calls remain explicit abstract transitions, not certified execution.
    pub machine_memory_inputs: Option<FrameMemoryInputs>,
    /// Exact theorem this request must eventually instantiate with checked
    /// allocation/placement/trace inputs; the name itself grants no authority.
    pub required_semr_theorem: &'static str,
    pub outstanding: Vec<FrameInputObligation>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProducerSavedPair {
    pub first_hardware_register: u8,
    pub second_hardware_register: u8,
    pub floating_point: bool,
    /// Retained verbatim; never interpreted as the actual STP/LDP address.
    pub legacy_fp_offset: i32,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProducerFrameLayout {
    pub total_frame_bytes: u32,
    pub callee_saved_bytes: u32,
    pub spill_bytes: u32,
    pub local_bytes: u32,
    pub outgoing_argument_bytes: u32,
    pub uses_frame_pointer: bool,
    pub is_leaf: bool,
    pub uses_red_zone: bool,
    pub fp_to_spill_offset: i32,
    pub dynamic_allocation: bool,
    pub saved_pairs: Vec<ProducerSavedPair>,
}

impl From<&trust_cg_codegen::frame::FrameLayout> for ProducerFrameLayout {
    fn from(layout: &trust_cg_codegen::frame::FrameLayout) -> Self {
        Self {
            total_frame_bytes: layout.total_frame_size,
            callee_saved_bytes: layout.callee_saved_area_size,
            spill_bytes: layout.spill_area_size,
            local_bytes: layout.local_area_size,
            outgoing_argument_bytes: layout.outgoing_arg_area_size,
            uses_frame_pointer: layout.uses_frame_pointer,
            is_leaf: layout.is_leaf,
            uses_red_zone: layout.uses_red_zone,
            fp_to_spill_offset: layout.fp_to_spill_offset,
            dynamic_allocation: layout.has_dynamic_alloc,
            saved_pairs: layout
                .callee_saved_pairs
                .iter()
                .map(|pair| ProducerSavedPair {
                    first_hardware_register: trust_cg_ir::regs::hw_encoding(pair.reg1),
                    second_hardware_register: trust_cg_ir::regs::hw_encoding(pair.reg2),
                    floating_point: pair.is_fpr,
                    legacy_fp_offset: pair.fp_offset,
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameAccessInput {
    pub effect_index: usize,
    pub kind: FrameAccessKind,
    pub address: Formula,
    pub bytes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum FrameAccessKind {
    Read,
    Write,
}

impl From<crate::cer_memory::AccessKind> for FrameAccessKind {
    fn from(kind: crate::cer_memory::AccessKind) -> Self {
        match kind {
            crate::cer_memory::AccessKind::Read => Self::Read,
            crate::cer_memory::AccessKind::Write => Self::Write,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameStepInput {
    pub occurrence: usize,
    pub pc: u64,
    pub instruction: [u8; 4],
    pub path: Formula,
    pub pre_sp: Formula,
    pub memory_before: Formula,
    pub memory_after: Formula,
    pub accesses: Vec<FrameAccessInput>,
    pub control: crate::cer_memory_machine::Control,
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameCallInput {
    pub occurrence: usize,
    pub pc: u64,
    pub path: Formula,
    pub before: Formula,
    pub after: Formula,
    pub kind: crate::cer_memory_machine::CallKind,
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameReturnInput {
    pub occurrence: usize,
    pub pc: u64,
    pub path: Formula,
    pub memory: Formula,
    pub kind: crate::cer_memory_machine::ExitKind,
}

/// Preserve the actual entry parameterization, including unspecified register
/// bits. Neither a pointer image nor an ABI guarantee is inferred from it.
#[derive(Clone, Debug, Serialize)]
pub struct FrameEntryInput {
    pub gpr: [Formula; 31],
    pub fpr: [Formula; 32],
    pub sp: Formula,
    pub pc: Formula,
    pub flags: [Formula; 4],
    pub memory: Formula,
}

#[derive(Clone, Debug, Serialize)]
pub struct FrameMemoryInputs {
    pub entry: FrameEntryInput,
    pub steps: Vec<FrameStepInput>,
    pub calls: Vec<FrameCallInput>,
    pub returns: Vec<FrameReturnInput>,
}

fn memory_inputs(
    pending: &crate::cer_memory_machine::PendingMachineMemory,
) -> Option<FrameMemoryInputs> {
    if pending.steps().len() > 64 || pending.calls().len() > 16 || pending.exits().len() > 16 {
        return None;
    }
    let entry = pending.entry();
    let input = FrameMemoryInputs {
        entry: FrameEntryInput {
            gpr: entry.gpr.clone(),
            fpr: entry.fpr.clone(),
            sp: entry.sp.clone(),
            pc: entry.pc.clone(),
            flags: [
                entry.flags.n.clone(),
                entry.flags.z.clone(),
                entry.flags.c.clone(),
                entry.flags.v.clone(),
            ],
            memory: entry.memory.clone(),
        },
        steps: pending
            .steps()
            .iter()
            .enumerate()
            .map(|(occurrence, step)| FrameStepInput {
                occurrence,
                pc: step.pc,
                instruction: step.instruction,
                path: step.path.clone(),
                pre_sp: step.pre_sp.clone(),
                memory_before: step.memory_before.clone(),
                memory_after: step.memory_after.clone(),
                accesses: step
                    .accesses
                    .iter()
                    .map(|access| FrameAccessInput {
                        effect_index: access.effect_index,
                        kind: access.kind.into(),
                        address: access.address.clone(),
                        bytes: access.width_bytes,
                    })
                    .collect(),
                control: step.control,
            })
            .collect(),
        calls: pending
            .calls()
            .iter()
            .map(|call| FrameCallInput {
                occurrence: call.step,
                pc: call.pc,
                path: call.path.clone(),
                before: call.before.clone(),
                after: call.after.clone(),
                kind: call.kind,
            })
            .collect(),
        returns: pending
            .exits()
            .iter()
            .map(|exit| FrameReturnInput {
                occurrence: exit.step,
                pc: exit.pc,
                path: exit.path.clone(),
                memory: exit.bytes.clone(),
                kind: exit.kind,
            })
            .collect(),
    };
    // This limit bounds diagnostic retention only. Its failure leaves every
    // required proof obligation pending and never changes an execution grade.
    serde_json::to_vec(&input).ok().filter(|bytes| bytes.len() <= 1 << 20).map(|_| input)
}

fn outstanding() -> Vec<FrameInputObligation> {
    use FrameInputObligation::*;
    vec![
        SemRAllocationEmbedding,
        SourceArgumentPointerImages,
        ActualSpFramePlacement,
        CompleteInstructionMemoryRefinement,
        CallFrameOwnershipAndMemoryRely,
        SavedRegistersAndReturnTarget,
        OriginalUnrestrictedArrayEquation,
    ]
}

fn words(window: &FunctionWindow) -> Option<Vec<u32>> {
    (window.code.len() % 4 == 0).then(|| {
        window.code.chunks_exact(4).map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]])).collect()
    })
}

fn envelope(window: &FunctionWindow, observed: &AotFrameLayoutObservation) -> FrameEnvelopeInput {
    let Some(layout) = &observed.layout else {
        return FrameEnvelopeInput::MissingProducerLayout;
    };
    let unsupported = |reason: &str| FrameEnvelopeInput::Unsupported { reason: reason.into() };
    if layout.total_frame_size != 16
        || layout.callee_saved_area_size != 16
        || layout.spill_area_size != 0
        || layout.local_area_size != 0
        || layout.outgoing_arg_area_size != 0
        || !layout.uses_frame_pointer
        || layout.is_leaf
        || layout.uses_red_zone
        || layout.has_dynamic_alloc
        || !observed.stack_slots.is_empty()
    {
        return unsupported(
            "no complete frame-16/no-slot instruction witness for this producer layout",
        );
    }
    if layout.callee_saved_pairs.len() != 1 {
        return unsupported("producer saved-register population differs from the FP/LR envelope");
    }
    let pair = &layout.callee_saved_pairs[0];
    if pair.reg1 != X29 || pair.reg2 != X30 || pair.is_fpr {
        return unsupported("producer saved-register identities differ from the FP/LR envelope");
    }
    // These are the actual five instructions of the observed b8 O0 caller,
    // including the saved registers, signed writeback and return register.
    // The check binds an input shape only: BL may still destroy saved bytes
    // through a source pointer, so this cannot prove the return state.
    let Some(code) = words(window) else {
        return unsupported("partial instruction word");
    };
    if code.len() != 5
        || code[0] != 0xa9bf_7bfd
        || code[1] != 0x9100_03fd
        || code[2] & 0xfc00_0000 != 0x9400_0000
        || code[3] != 0xa8c1_7bfd
        || code[4] != 0xd65f_03c0
        || !window.unknown.is_empty()
        || !window.data_in_code.is_empty()
        || window.reachable != (0..5).map(|i| window.start + i * 4).collect()
    {
        return unsupported("actual complete bytes differ from the frame-16/direct-call envelope");
    }
    let call_pc = window.start + 8;
    if window.sites.len() != 1 {
        return unsupported("actual call census differs");
    }
    let site = &window.sites[0];
    if site.offset != call_pc || site.kind != MachineSiteKind::Call || site.in_trap_tail {
        return unsupported("actual call site differs");
    }
    let Some(callee) = &site.callee else {
        return unsupported("actual callee is unresolved");
    };
    FrameEnvelopeInput::ObservedFpLr16DirectCall { call_pc, callee: callee.clone() }
}

/// Used only with the actual result of the same Compiler invocation in F1.
/// Rebind every function/object/placement; attach requests without changing
/// any proof verdict. Public proof replay continues to rebuild its full goal.
pub(crate) fn attach(
    input: &CerInput<'_>,
    observed: &[AotFrameLayoutObservation],
    report: &mut CerReport,
) -> Result<(), String> {
    if report.object_sha256 != artifact_digest(input.object) {
        return Err("frame request/report object binding differs".into());
    }
    let object = CompiledObject::parse(input.object).map_err(|e| e.to_string())?;
    let expected =
        ObjectExpectations::from_module(input.m_cg, object.format, input.relocation_model)
            .map_err(|e| e.to_string())?;
    let object = ObjectLayout::bind(object, &expected).map_err(|e| e.to_string())?;
    let mut by_name = BTreeMap::new();
    for row in observed {
        if by_name.insert(row.symbol.as_str(), row).is_some() {
            return Err("duplicate actual Compiler frame symbol".into());
        }
    }
    let names: BTreeSet<_> = object.windows.keys().map(String::as_str).collect();
    if names != by_name.keys().copied().collect() {
        return Err("actual Compiler frame/object population differs".into());
    }
    // No framed request means no allocation index or whole-module hash. For
    // actual requests, share one fresh binding across the entire object.
    let allocation_request = std::cell::OnceCell::new();
    for certificate in &mut report.certificates {
        // The full internal observer is temporary. Frameless functions keep
        // no duplicate trace, and framed requests retain only bounded inputs.
        let execution = certificate.frame_execution.take();
        let window = object
            .windows
            .get(&certificate.symbol)
            .ok_or("frame certificate is not in the actual object")?;
        let row = by_name[certificate.symbol.as_str()];
        if certificate.text_sha256 != window.text_sha256() {
            return Err("frame certificate changes the actual function bytes".into());
        }
        let starts_with_frame =
            words(window).is_some_and(|words| words.first() == Some(&0xa9bf_7bfd));
        if row.layout.as_ref().is_some_and(|layout| layout.total_frame_size == 0) {
            if starts_with_frame {
                return Err("zero producer frame contradicts actual FP/LR allocation".into());
            }
            continue;
        }
        // A framed function with no P entry already grades Unknown ("P has no placement for
        // this function", `call_event`), so its frame request has nothing to bind to: retain
        // nothing for it. Refusing the module here changed the verdict this function keeps (a
        // module-level `[f1-output-gate:binding]` even under allow-unknown), which `attach`
        // must never do; the output gate still judges that row.
        let Some(placement) = input.placements.get(&certificate.symbol) else {
            continue;
        };
        let observation = certificate.memory_observation.as_ref();
        certificate.frame_inputs = Some(PendingFrameInput {
            schema: "trust.pending-semR-frame-input.v2",
            symbol: certificate.symbol.clone(),
            object_sha256: report.object_sha256.clone(),
            text_sha256: certificate.text_sha256.clone(),
            placement_sha256: placement.digest(),
            producer_ir_sha256: certificate.producer_ir_sha256.clone(),
            producer_frame_bytes: row.layout.as_ref().map(|layout| layout.total_frame_size),
            producer_slot_count: row.stack_slots.len(),
            producer_layout: row.layout.as_ref().map(ProducerFrameLayout::from),
            producer_slots: row.stack_slots.clone(),
            source_stack_allocations: allocation_request
                .get_or_init(|| AotSourceAllocationRequest::new(input.object, input.m_cg))
                .as_ref()
                .map_err(Clone::clone)
                .and_then(|request| row.bound_source_stack_allocations_for(request).cloned())
                .map_err(|reason| {
                    format!("source allocation inputs unavailable; exact adapter-source/lineage required: {reason}")
                }),
            entry_sp: observation.and_then(|o| o.entry_sp.clone()),
            entry_memory_sha256: observation.and_then(|o| o.entry_memory_sha256.clone()),
            envelope: envelope(window, row),
            machine_memory_inputs: execution.as_ref().and_then(memory_inputs),
            required_semr_theorem: "SemR.MemoryEmbedding.PlacedFrameInput.preserves",
            outstanding: outstanding(),
        });
    }
    Ok(())
}

/// Most rows one refusal names; the certificates JSON keeps every one.
const MAX_ROWS: usize = 16;
/// Most characters of one obligation detail a refusal quotes.
const MAX_DETAIL: usize = 320;

/// What a refusal adds after `ships`' own text, under the `policy` it refused.
///
/// When a function is Refuted, `ships` refuses under every policy and the
/// refutation is the only cause: this names each refuting obligation and
/// nothing else. Otherwise, under Strict only, it names for each function the
/// closure left unclosed the thing that keeps it out of closed-[PROVED] (a
/// Refuted or else its first Unknown obligation, missing kernel evidence, or
/// unclosed callees), then the SemR frame request, labelled as a request:
/// `attach` runs after grading and gives every framed function the same
/// pending list, so the list decides no grade and must not read as the cause.
/// The text starts with its own label ("refuted by:" or "blockers:") so the
/// reader can tell it from `ships`' list, and carries no `[tag]` the F1 ladder
/// would read as a refusal class.
pub(crate) fn refusal_context(report: &CerReport, policy: EmitPolicy) -> String {
    let refuted: Vec<&FunctionCertificate> = report
        .certificates
        .iter()
        .filter(|c| matches!(c.verdict, OutputVerdict::Refuted { .. }))
        .collect();
    if !refuted.is_empty() {
        let entries = refuted.into_iter().flat_map(refutations).collect();
        return format!("refuted by: {}", capped(entries));
    }
    if policy != EmitPolicy::StrictProvenOnly || report.closure.unclosed.is_empty() {
        return String::new();
    }
    let rows: Vec<(&Unclosed, Option<&FunctionCertificate>)> =
        report.closure.unclosed.iter().map(|u| (u, report.certificate(&u.symbol))).collect();
    let mut entries = vec![capped(rows.iter().map(|(u, c)| blocker(u, *c)).collect())];
    // One request per distinct outstanding list, naming every function that carries it.
    let mut requests: Vec<(String, Vec<String>)> = Vec::new();
    for input in rows.iter().filter_map(|(_, c)| c.and_then(|c| c.frame_inputs.as_ref())) {
        let list = format!("{:?}", input.outstanding);
        let symbol = format!("`{}`", input.symbol);
        match requests.iter_mut().find(|(l, _)| *l == list) {
            Some((_, symbols)) => symbols.push(symbol),
            None => requests.push((list, vec![symbol])),
        }
    }
    for (list, symbols) in requests {
        let mut named = symbols.iter().take(MAX_ROWS).cloned().collect::<Vec<_>>().join(", ");
        if symbols.len() > MAX_ROWS {
            named.push_str(&format!(" and {} more", symbols.len() - MAX_ROWS));
        }
        entries
            .push(untagged(&format!("PKG-B SemR request (decides no grade) from {named}: {list}")));
    }
    format!("blockers: {}", entries.join("; "))
}

/// At most [`MAX_ROWS`] of `entries`, each untagged, joined, and a count of the rest.
fn capped(entries: Vec<String>) -> String {
    let rest = entries.len().saturating_sub(MAX_ROWS);
    let mut out: Vec<String> = entries.iter().take(MAX_ROWS).map(|e| untagged(e)).collect();
    if rest > 0 {
        out.push(format!("... and {rest} more (the certificates JSON names every one)"));
    }
    out.join("; ")
}

/// `detail` cut to [`MAX_DETAIL`] characters, or a stand-in when it is empty.
fn clipped(detail: &str) -> String {
    if detail.trim().is_empty() {
        return "no reason recorded".into();
    }
    match detail.char_indices().nth(MAX_DETAIL) {
        Some((cut, _)) => format!("{}... (+{} bytes)", &detail[..cut], detail.len() - cut),
        None => detail.to_string(),
    }
}

/// `certificate`'s obligations in order, numbered as the certificate numbers them.
fn obligations(certificate: &FunctionCertificate) -> [(&'static str, &ObligationGrade); 6] {
    let o = &certificate.obligations;
    [
        ("o0", &o.o0_abi),
        ("o1", &o.o1_binding),
        ("o2", &o.o2_pairing),
        ("o3", &o.o3_events),
        ("o4", &o.o4_return),
        ("o5", &o.o5_frame),
    ]
}

/// Each Refuted obligation of a Refuted `certificate`, or its verdict's own
/// account when no obligation is Refuted.
fn refutations(certificate: &FunctionCertificate) -> Vec<String> {
    let symbol = &certificate.symbol;
    let refuted: Vec<String> = obligations(certificate)
        .iter()
        .filter(|(_, g)| g.grade == Grade::Refuted)
        .map(|(n, g)| format!("{symbol} {n}: Refuted: {}", clipped(&g.detail)))
        .collect();
    if !refuted.is_empty() {
        return refuted;
    }
    match &certificate.verdict {
        OutputVerdict::Refuted { detail } => {
            vec![format!("{symbol}: Refuted: {}", clipped(detail))]
        }
        other => {
            vec![format!("{symbol}: {}: {}", certificate.grade, clipped(&format!("{other:?}")))]
        }
    }
}

/// The first reason `unclosed`'s function is not closed-[PROVED]: a Refuted
/// obligation before any Unknown one, since any Refuted obligation decides the
/// verdict whatever order the gate graded them in.
fn blocker(unclosed: &Unclosed, certificate: Option<&FunctionCertificate>) -> String {
    let symbol = &unclosed.symbol;
    let Some(certificate) = certificate else {
        return format!("{symbol}: no certificate");
    };
    let callees = || {
        let named = unclosed.blocked_by.iter().map(|c| format!("`{c}`")).collect::<Vec<_>>();
        format!("blocked by callees [{}]", named.join(", "))
    };
    if certificate.verdict.is_kernel_proved() {
        return format!("{symbol}: {}", callees());
    }
    if certificate.verdict.is_proven() {
        return if unclosed.blocked_by.is_empty() {
            format!("{symbol}: Proven without kernel evidence")
        } else {
            format!("{symbol}: Proven without kernel evidence, and {}", callees())
        };
    }
    let ordered = obligations(certificate);
    let first = |grade: Grade| ordered.iter().find(|(_, g)| g.grade == grade);
    match first(Grade::Refuted).or_else(|| first(Grade::Unknown)) {
        Some((n, g)) => format!("{symbol} {n}: {:?}: {}", g.grade, clipped(&g.detail)),
        // Not Proven with no Unknown or Refuted obligation: the verdict's own account
        // (for instance, an obligation was never reached).
        None => match &certificate.verdict {
            OutputVerdict::Unknown { reason } => format!("{symbol}: Unknown: {}", clipped(reason)),
            OutputVerdict::Refuted { detail } => format!("{symbol}: Refuted: {}", clipped(detail)),
            other => {
                format!("{symbol}: {}: {}", certificate.grade, clipped(&format!("{other:?}")))
            }
        },
    }
}

/// `text` with every `[tag]` the F1 ladder would read as a refusal class
/// (`scripts/trust_f1_ladder.py` `CLASS_TAG`, `\[[a-z][a-z0-9:-]*\]`) quoted
/// as "[`tag`]": an obligation detail or callee name is not a refusal class.
fn untagged(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(open) = rest.find('[') {
        out.push_str(&rest[..open]);
        let after = &rest[open + 1..];
        let len = after
            .bytes()
            .take_while(|b| {
                b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b':' | b'-')
            })
            .count();
        let tag = after.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
            && after.as_bytes().get(len) == Some(&b']');
        if tag {
            out.push_str("[`");
            out.push_str(&after[..len]);
            out.push_str("`]");
            rest = &after[len + 1..];
        } else {
            out.push('[');
            rest = after;
        }
    }
    out.push_str(rest);
    out
}

#[cfg(all(test, feature = "kernel-recheck"))]
#[path = "compiler_frame_inputs/tests.rs"]
mod tests;
