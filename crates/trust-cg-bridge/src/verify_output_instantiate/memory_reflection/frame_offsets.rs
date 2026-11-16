//! Retained CLOSED offset theorems, checked before use in model-v3 proofs.
use super::*;
use crate::original_conjunction_certificate::TermPacket;
pub(super) fn install(env: &mut clean_kernel::Environment) -> Result<(), String> {
    let packets: Vec<TermPacket> =
        serde_json::from_slice(include_bytes!("frame_bank/offsets.json"))
            .map_err(|e| e.to_string())?;
    if packets.len() != 120 {
        return Err("fixed frame-offset theorem population".into());
    }
    let mut packets = packets.into_iter();
    for i in 1..16 {
        for j in 0..i {
            let (goal, proof) = packets.next().ok_or("missing frame-offset theorem")?.restore()?;
            let expected =
                frame_offset_model::statement(i, j).ok_or("invalid frame-offset statement")?;
            if goal != expected {
                return Err("fixed frame-offset FULL64 statement mismatch".into());
            }
            clean_kernel::TypeChecker::with_mode(env, env.mode())
                .check_type(&proof, &expected)
                .map_err(|e| format!("fixed frame-offset kernel refusal: {e:?}"))?;
            let name = Name::from_string(&frame_offset_model::name(i, j));
            env.add_decl(clean_kernel::Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: expected,
                value: proof,
            })
            .map_err(|e| format!("fixed frame-offset declaration: {e:?}"))?;
            if !env.axiom_deps(&name).ok_or("fixed frame-offset closure unavailable")?.is_empty() {
                return Err("fixed frame-offset logical axiom dependency".into());
            }
        }
    }
    frame_reads::install(env)
}
pub(super) fn instance(bits: &[Expr; 64], left: &[i128], right: &[i128]) -> Option<Expr> {
    let i = frame_offset_model::index(left)?;
    let j = frame_offset_model::index(right)?;
    if i <= j {
        return None;
    }
    Some(Expr::apps(Expr::const_str(&frame_offset_model::name(i, j)), bits.iter().cloned()))
}
