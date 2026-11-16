//! Fixed retained mathematical lemmas. Restore, match the independently built
//! FULL64-bit statement, and actually kernel-check; never regenerate proofs.
use super::*;
use crate::original_conjunction_certificate::TermPacket;
fn nat(n: u32) -> Expr {
    match n {
        0 => Expr::const_str("Nat.zero"),
        1 | 2 => Expr::app(Expr::const_str("Nat.succ"), nat(n - 1)),
        _ => {
            let twice = Expr::apps(Expr::const_str("Nat.mul"), [nat(2), nat(n / 2)]);
            if n % 2 == 0 { twice } else { Expr::app(Expr::const_str("Nat.succ"), twice) }
        }
    }
}
fn zeros(n: u32) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.bvReplF"), nat(n))
}
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [a, b])
}
fn statement(k: u32) -> Expr {
    let byte = (0..8).rev().fold(kx::nil(), |tail, i| kx::cons(Expr::bvar(7 - i), tail));
    let widened = Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [byte.clone(), nat(56)]);
    let lhs = Expr::apps(Expr::const_str("Clean.BVC.bvShl"), [widened, kx::bits(k as i128, 64)]);
    let rhs = append(zeros(k), append(byte, zeros(56 - k)));
    let mut ty = equality(kx::list_bool(), lhs, rhs);
    for _ in 0..8 {
        ty = Expr::pi(BinderInfo::Default, kx::bool_ty(), ty)
    }
    ty
}
fn payload(k: u32) -> Option<&'static [u8]> {
    Some(match k {
        8 => include_bytes!("frame_bank/shift-8.json"),
        16 => include_bytes!("frame_bank/shift-16.json"),
        24 => include_bytes!("frame_bank/shift-24.json"),
        32 => include_bytes!("frame_bank/shift-32.json"),
        40 => include_bytes!("frame_bank/shift-40.json"),
        48 => include_bytes!("frame_bank/shift-48.json"),
        56 => include_bytes!("frame_bank/shift-56.json"),
        _ => return None,
    })
}
pub(super) fn install(env: &mut clean_kernel::Environment) -> Result<(), String> {
    for k in [8, 16, 24, 32, 40, 48, 56] {
        let wire = payload(k).ok_or("missing fixed byte-shift proof")?;
        let data: TermPacket = serde_json::from_slice(wire).map_err(|e| e.to_string())?;
        let (goal, proof) = data.restore()?;
        let expected = statement(k);
        if goal != expected {
            return Err("fixed byte-shift original FULL64 statement mismatch".into());
        }
        clean_kernel::TypeChecker::with_mode(env, env.mode())
            .check_type(&proof, &expected)
            .map_err(|e| format!("fixed byte-shift kernel rejection: {e:?}"))?;
        let name = Name::from_string(&format!("Clean.FrameByteShiftV1.shl{k}"));
        env.add_decl(clean_kernel::Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: expected,
            value: proof,
        })
        .map_err(|e| format!("fixed byte-shift environment insertion: {e:?}"))?;
        if !env.axiom_deps(&name).ok_or("fixed byte-shift axiom closure unavailable")?.is_empty() {
            return Err("fixed byte-shift lemma has a logical axiom dependency".into());
        }
    }
    frame_offsets::install(env)
}
pub(super) fn instance(k: u32, bits: &[Expr]) -> Option<Expr> {
    if bits.len() != 8 || payload(k).is_none() {
        return None;
    }
    Some(Expr::apps(
        Expr::const_str(&format!("Clean.FrameByteShiftV1.shl{k}")),
        bits.iter().cloned(),
    ))
}
