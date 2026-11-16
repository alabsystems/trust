// Copyright 2026 Andrew Yates | Apache-2.0
use trust_machine_sem::{Aarch64Semantics, Effect, Semantics};
use trust_types::Sort;

use super::super::*;
use crate::cer_memory_machine::{CallKind, Control, ExitKind};
use crate::compiled_object::MachineSiteKind;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CallerSubject {
    pub source: SubjectBinding,
    pub symbol: String,
    pub caller_binding: String,
    pub callee_binding: String,
    pub callee_symbol: String,
    pub call_pc: u64,
    pub instructions: [[u8; 4]; 5],
    pub states_sha256: String,
}
pub(super) struct CallerTrace<'a> {
    pub entry: &'a MachineState,
    pub save_after: &'a MachineState,
    pub call_before: &'a MachineState,
    pub modeled_after: &'a MachineState,
    pub restore_before: &'a MachineState,
    pub restore_after: &'a MachineState,
    pub return_before: &'a MachineState,
    pub return_target: Formula,
    pub fresh_post: &'a Formula,
    pub subject: CallerSubject,
}
fn selected_equal(left: &MachineState, right: &MachineState) -> bool {
    left.sp == right.sp
        && left.memory == right.memory
        && left.gpr[29] == right.gpr[29]
        && left.gpr[30] == right.gpr[30]
}
fn state_equal(left: &MachineState, right: &MachineState) -> Result<bool, String> {
    Ok(digest(&StateImage::from(left))? == digest(&StateImage::from(right))?)
}

/// Bind a real closed five-instruction frame envelope. This is a required
/// original-input selector, not a claim about the abstract call's physical rely.
pub(super) fn bind<'a>(
    input: &CerInput<'_>,
    certificate: &'a FunctionCertificate,
) -> Result<CallerTrace<'a>, String> {
    let pending = certificate.frame_execution.as_ref().ok_or("no actual caller observation")?;
    let source = SubjectBinding::from_input(input, certificate)?;
    if certificate.frame_step_subject.as_ref() != Some(&source) {
        return Err("caller source/P custody differs".into());
    }
    let bound =
        BoundFunction::bind(input.object, input.m_cg, &certificate.symbol, input.relocation_model)?;
    let window = bound.window();
    if digest(pending.binding())? != digest(bound.binding())?
        || certificate.extent != (window.start, window.end)
        || certificate.text_sha256 != window.text_sha256()
    {
        return Err("caller object/module/extent binding differs".into());
    }
    if pending.steps().len() != 5
        || pending.calls().len() != 1
        || pending.exits().len() != 1
        || window.code.len() != 20
        || window.reachable.len() != 5
        || window.start % 4 != 0
    {
        return Err("caller is outside the exact five-step frame envelope".into());
    }
    let call = &pending.calls()[0];
    let exit = &pending.exits()[0];
    if call.step != 2
        || call.pc != window.start + 8
        || call.kind != CallKind::Call
        || exit.step != 4
        || exit.kind != ExitKind::Return
        || exit.pc != window.start + 16
    {
        return Err("actual caller call/return census differs".into());
    }
    let mut states = Vec::new();
    let mut words = Vec::new();
    for (index, step) in pending.steps().iter().enumerate() {
        let pc = window.start + 4 * index as u64;
        let (before, after) = pending.states_at(index)?;
        if step.pc != pc
            || step.path != Formula::Bool(true)
            || window.code.get(index * 4..index * 4 + 4) != Some(step.instruction.as_slice())
            || step.pre_sp != before.sp
            || step.memory_before != before.memory
        {
            return Err("actual caller step/entry/bytes differ".into());
        }
        if index == 0 && !state_equal(before, pending.entry())? {
            return Err("caller entry snapshot differs".into());
        }
        if index + 1 < 5 && !state_equal(after, pending.states_at(index + 1)?.0)? {
            return Err("actual callback state chain is not adjacent".into());
        }
        let decoded = trust_disasm::decode_aarch64(&step.instruction, pc)
            .map_err(|e| format!("caller decode: {e:?}"))?;
        let effects = Aarch64Semantics
            .effects(before, &decoded)
            .map_err(|e| format!("caller effects: {e:?}"))?;
        if effects != step.effects {
            return Err("actual caller effect vector differs from decoding".into());
        }
        let expected = match index {
            2 => Control::Call,
            4 => Control::Return,
            _ => Control::Ordinary,
        };
        if step.control != expected {
            return Err("caller control census differs".into());
        }
        if index != 2 && step.memory_after != after.memory {
            return Err("ordinary callback memory differs".into());
        }
        states.push((StateImage::from(before), StateImage::from(after)));
        words.push(step.instruction);
    }
    let (entry, save_after) = pending.states_at(0)?;
    let (call_before, modeled_after) = pending.states_at(2)?;
    let (restore_before, restore_after) = pending.states_at(3)?;
    let (return_before, _) = pending.states_at(4)?;
    if call.before != call_before.memory
        || call.after != modeled_after.memory
        || exit.bytes != return_before.memory
    {
        return Err("call/return snapshots differ from actual callback states".into());
    }
    let save = frame_pair::bind(pending.steps()[0].instruction, window.start, entry)?;
    let restore =
        frame_pair::bind(pending.steps()[3].instruction, window.start + 12, restore_before)?;
    if save.role() != frame_pair::PairRole::Save
        || restore.role() != frame_pair::PairRole::Restore
        || !selected_equal(save.post(), save_after)
        || !selected_equal(restore.post(), restore_after)
    {
        return Err("actual FP/LR/SP/memory pair state differs from canonical effects".into());
    }
    // The call model must remain visibly abstract. Peel the complete observed
    // Store tree only to recover its real raw-array parameter; the CIC goal
    // checks equality to the precise saved-byte expression, not this census.
    let mut fresh_post = &modeled_after.memory;
    let mut stores = 0;
    while let Formula::Store(previous, _, _) = fresh_post {
        fresh_post = previous;
        stores += 1;
        if stores > 16 {
            return Err("extra modeled caller store".into());
        }
    }
    if stores != 16
        || !matches!(fresh_post,Formula::Var(_,Sort::Array(index,value)) if **index==Sort::BitVec(64)&&**value==Sort::BitVec(8))
    {
        return Err("modeled call post-memory has an unsupported exact Store image".into());
    }
    let site = window.site_at(call.pc).ok_or("bound actual call site is absent")?;
    if site.kind != MachineSiteKind::Call || window.sites.len() != 1 {
        return Err("caller has extra/unbound call sites".into());
    }
    let callee_symbol = site.callee.as_ref().ok_or("actual call has no owned callee")?;
    let callee =
        BoundFunction::bind(input.object, input.m_cg, callee_symbol, input.relocation_model)?;
    if !input.bodies.contains_key(callee_symbol) || !input.placements.contains_key(callee_symbol) {
        return Err("actual callee source body/P is absent".into());
    }
    let return_target = pending.steps()[4]
        .effects
        .iter()
        .find_map(|effect| match effect {
            Effect::Return { target } => Some(target.clone()),
            _ => None,
        })
        .ok_or("actual RET target is absent")?;
    let subject = CallerSubject {
        source,
        symbol: certificate.symbol.clone(),
        caller_binding: digest(bound.binding())?,
        callee_binding: digest(callee.binding())?,
        callee_symbol: callee_symbol.clone(),
        call_pc: call.pc,
        instructions: words.try_into().map_err(|_| "caller instruction count")?,
        states_sha256: digest(&states)?,
    };
    Ok(CallerTrace {
        entry,
        save_after,
        call_before,
        modeled_after,
        restore_before,
        restore_after,
        return_before,
        return_target,
        fresh_post,
        subject,
    })
}
