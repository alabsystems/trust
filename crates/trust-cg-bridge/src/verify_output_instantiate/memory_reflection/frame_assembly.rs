//! Retained universally checked eight-byte little-endian reconstruction.
//! The complete original Nat-shift/OR expression is its actual left endpoint.
use super::*;
use crate::original_conjunction_certificate::TermPacket;
fn statement() -> Expr {
    let bits: [Expr; 64] = std::array::from_fn(|i| Expr::bvar(63 - i as u32));
    let mut word = frame_word_model::byte(frame_read_model::list(&bits[..8]), 0);
    for k in 1..8 {
        word = Expr::apps(
            Expr::const_str("Clean.BVC.bvZipOr"),
            [word, frame_word_model::byte(frame_read_model::list(&bits[k * 8..k * 8 + 8]), k)],
        );
    }
    let mut goal = equality(kx::list_bool(), word, frame_read_model::list(&bits));
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, kx::bool_ty(), goal);
    }
    goal
}
pub(super) fn install(env: &mut clean_kernel::Environment) -> Result<(), String> {
    let packet: TermPacket = serde_json::from_slice(include_bytes!("frame_bank/assembly.json"))
        .map_err(|e| e.to_string())?;
    let (goal, proof) = packet.restore()?;
    let expected = statement();
    if goal != expected {
        return Err("fixed frame-assembly ORIGINAL FULL64 statement mismatch".into());
    }
    clean_kernel::TypeChecker::with_mode(env, env.mode())
        .check_type(&proof, &expected)
        .map_err(|e| format!("fixed frame-assembly kernel refusal: {e:?}"))?;
    let name = Name::from_string("Clean.FrameWordAssemblyV1.reconstruct");
    env.add_decl(clean_kernel::Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: expected,
        value: proof,
    })
    .map_err(|e| format!("fixed frame-assembly insertion: {e:?}"))?;
    if !env.axiom_deps(&name).ok_or("fixed frame-assembly closure unavailable")?.is_empty() {
        return Err("fixed frame-assembly logical axiom dependency".into());
    }
    Ok(())
}
pub(super) fn instance(bits: &[Expr; 64]) -> Expr {
    Expr::apps(Expr::const_str("Clean.FrameWordAssemblyV1.reconstruct"), bits.iter().cloned())
}
