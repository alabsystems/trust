// Copyright 2026 Andrew Yates | Apache-2.0
use trust_machine_sem::{Aarch64Semantics, Effect, Semantics};
use trust_types::{Formula, Sort};

use super::super::super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CalleeSubject {
    pub caller: super::super::binding::CallerSubject,
    pub callee_source: SubjectBinding,
    pub instructions: [[u8; 4]; 5],
    pub call_data_sha256: String,
    pub data_states_sha256: String,
    pub store_step: usize,
}

pub(super) struct CalleeTrace {
    pub entry: MachineState,
    pub before: MachineState,
    pub after: MachineState,
    pub destination: Formula,
    pub byte: Formula,
    pub call_return: Formula,
    pub return_target: Formula,
    pub subject: CalleeSubject,
}

/// A lossless typed image of every effect this bounded envelope accepts.
/// Effect itself deliberately has no serialization API.
#[derive(Serialize)]
enum EffectImage<'a> {
    RegWrite { index: u8, width: u32, value: &'a Formula },
    MemRead { address: &'a Formula, width_bytes: u32 },
    MemWrite { address: &'a Formula, value: &'a Formula, width_bytes: u32 },
    PcUpdate { value: &'a Formula },
    Call { target: &'a Formula, return_addr: &'a Formula },
    Return { target: &'a Formula },
}

fn effect_images(effects: &[Effect]) -> Result<Vec<EffectImage<'_>>, String> {
    effects
        .iter()
        .map(|effect| {
            Ok(match effect {
                Effect::RegWrite { index, width, value } => {
                    EffectImage::RegWrite { index: *index, width: *width, value }
                }
                Effect::MemRead { address, width_bytes } => {
                    EffectImage::MemRead { address, width_bytes: *width_bytes }
                }
                Effect::MemWrite { address, value, width_bytes } => {
                    EffectImage::MemWrite { address, value, width_bytes: *width_bytes }
                }
                Effect::PcUpdate { value } => EffectImage::PcUpdate { value },
                Effect::Call { target, return_addr } => EffectImage::Call { target, return_addr },
                Effect::Return { target } => EffectImage::Return { target },
                _ => return Err("effect outside the exact serialized callee envelope".into()),
            })
        })
        .collect()
}

/// Interpret only the actual closed callee's decoded data-effect envelope.
/// This does not replace CER's call rely, assert physical fetching, or infer
/// that an arbitrary raw pointer is outside the caller's private frame.
pub(super) fn observe(input: &CerInput<'_>, caller: &str) -> Result<CalleeTrace, String> {
    let report = crate::call_event::observe_compiled_module_for_frame(input)
        .map_err(|error| error.to_string())?;
    let certificate = report
        .certificates
        .iter()
        .find(|row| row.symbol == caller)
        .ok_or("actual caller certificate is absent")?;
    let trace = super::super::binding::bind(input, certificate)?;
    let callee = BoundFunction::bind(
        input.object,
        input.m_cg,
        &trace.subject.callee_symbol,
        input.relocation_model,
    )?;
    let callee_certificate = report
        .certificates
        .iter()
        .find(|row| row.symbol == trace.subject.callee_symbol)
        .ok_or("actual callee certificate is absent")?;
    let callee_source = SubjectBinding::from_input(input, callee_certificate)?;
    let window = callee.window();
    if window.code.len() != 20
        || window.reachable.len() != 5
        || !window.sites.is_empty()
        || window.start % 4 != 0
    {
        return Err("callee is outside the closed five-step leaf envelope".into());
    }
    let call = trust_disasm::decode_aarch64(&trace.subject.instructions[2], trace.subject.call_pc)
        .map_err(|error| format!("actual BL decode: {error:?}"))?;
    let calls = Aarch64Semantics
        .effects(trace.call_before, &call)
        .map_err(|error| format!("actual BL effects: {error:?}"))?;
    let [
        Effect::Call { target, return_addr },
        Effect::RegWrite { index: 30, width: 64, value: lr_value },
        Effect::PcUpdate { value: pc_value },
    ] = calls.as_slice()
    else {
        return Err("actual BL has unexpected data effects".into());
    };
    if return_addr != lr_value || target != pc_value {
        return Err("decoded BL LR/PC expressions differ".into());
    }
    let mut before = trace.call_before.clone();
    // The decoded BL data effect writes this exact LR. No claim that PC
    // fetched these bytes is made by selecting the relocation-bound callee.
    before
        .apply_effects(&calls[1..])
        .map_err(|error| format!("actual BL data transition: {error:?}"))?;
    let call_data_sha256 = digest(&(
        StateImage::from(trace.call_before),
        effect_images(&calls)?,
        StateImage::from(&before),
    ))?;
    let mut state = before.clone();
    let mut states = Vec::new();
    let mut instructions = Vec::new();
    let mut stores = Vec::new();
    let mut return_target = None;
    for index in 0..5 {
        let pc = window.start + 4 * index as u64;
        let bytes: [u8; 4] = window.code[index * 4..index * 4 + 4]
            .try_into()
            .map_err(|_| "callee instruction width")?;
        let decoded = trust_disasm::decode_aarch64(&bytes, pc)
            .map_err(|error| format!("actual callee decode: {error:?}"))?;
        let expected_flow = if index == 4 {
            trust_disasm::ControlFlow::Return
        } else {
            trust_disasm::ControlFlow::Fallthrough
        };
        if decoded.flow != expected_flow {
            return Err(format!(
                "callee control flow is not straight-line before final RET: step {index} is {:?}",
                decoded.flow
            ));
        }
        let effects = Aarch64Semantics
            .effects(&state, &decoded)
            .map_err(|error| format!("actual callee effects: {error:?}"))?;
        let pre = digest(&StateImage::from(&state))?;
        let mut pc_updates = 0;
        for effect in &effects {
            match effect {
                Effect::RegWrite { index, width, .. }
                    if *index < 29 && matches!(*width, 32 | 64) => {}
                Effect::MemRead { width_bytes: 1, .. } => {}
                Effect::MemWrite { width_bytes: 1, .. } => stores.push(index),
                Effect::PcUpdate { .. } => pc_updates += 1,
                Effect::Return { target } if index == 4 && return_target.is_none() => {
                    return_target = Some(target.clone());
                }
                _ => return Err("callee has an unmodeled or frame-register data effect".into()),
            }
        }
        if pc_updates != 1 || (index == 4 && return_target.is_none()) {
            return Err("actual callee PC-update/final-RET census differs".into());
        }
        let effects_sha256 = digest(&effect_images(&effects)?)?;
        state
            .apply_effects(&effects)
            .map_err(|error| format!("actual callee data transition: {error:?}"))?;
        states.push((pre, effects_sha256, digest(&StateImage::from(&state))?));
        instructions.push(bytes);
    }
    let Some(return_target) = return_target.filter(|target| target == return_addr) else {
        return Err("actual callee single-store/SP/FP/LR/return census differs".into());
    };
    if stores.len() != 1
        || state.sp != before.sp
        || state.gpr[29] != before.gpr[29]
        || state.gpr[30] != before.gpr[30]
    {
        return Err("actual callee single-store/SP/FP/LR/return census differs".into());
    }
    let Formula::Store(previous, destination, byte) = &state.memory else {
        return Err("actual callee post-memory is not an exact byte Store".into());
    };
    if **previous != before.memory
        || trust_types::check_formula_sort(destination).ok() != Some(Sort::BitVec(64))
        || trust_types::check_formula_sort(byte).ok() != Some(Sort::BitVec(8))
    {
        return Err("actual callee store input/address/value differs".into());
    }
    let destination = *destination.clone();
    let byte = *byte.clone();
    let subject = CalleeSubject {
        caller: trace.subject,
        callee_source,
        instructions: instructions.try_into().map_err(|_| "callee instruction count")?,
        call_data_sha256,
        data_states_sha256: digest(&states)?,
        store_step: stores[0],
    };
    Ok(CalleeTrace {
        entry: trace.entry.clone(),
        before,
        after: state,
        destination,
        byte,
        call_return: return_addr.clone(),
        return_target,
        subject,
    })
}
