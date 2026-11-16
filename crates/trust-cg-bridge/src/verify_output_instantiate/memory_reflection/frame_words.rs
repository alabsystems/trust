//! Checked universal congruence transports the exact raw word expression.
//! This matcher supplies all original array/value/address operands; it cannot
//! grant proof authority without the final independently rebuilt goal check.
use super::*;
use crate::original_conjunction_certificate::TermPacket;
pub(super) fn install(env: &mut clean_kernel::Environment) -> Result<(), String> {
    let packets: Vec<TermPacket> = serde_json::from_slice(include_bytes!("frame_bank/words.json"))
        .map_err(|e| e.to_string())?;
    if packets.len() != 16 {
        return Err("fixed frame-word theorem population".into());
    }
    for (index, packet) in packets.into_iter().enumerate() {
        let which = index / 8;
        let count = index % 8 + 1;
        let (goal, proof) = packet.restore()?;
        let expected =
            frame_word_model::statement(which, count).ok_or("invalid frame-word statement")?;
        if goal != expected {
            return Err("fixed frame-word ORIGINAL operator statement mismatch".into());
        }
        clean_kernel::TypeChecker::with_mode(env, env.mode())
            .check_type(&proof, &expected)
            .map_err(|e| format!("fixed frame-word kernel refusal: {e:?}"))?;
        let name = Name::from_string(&frame_word_model::name(which, count));
        env.add_decl(clean_kernel::Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: expected,
            value: proof,
        })
        .map_err(|e| format!("fixed frame-word insertion: {e:?}"))?;
        if !env.axiom_deps(&name).ok_or("fixed frame-word closure unavailable")?.is_empty() {
            return Err("fixed frame-word logical axiom dependency".into());
        }
    }
    frame_assembly::install(env)
}
pub(super) fn reassembles_from(normal: &Formula, source: &Formula) -> bool {
    let mut parts = Vec::new();
    chunks(normal, &mut parts);
    if parts.len() != 8 {
        return false;
    }
    for (k, part) in parts.into_iter().enumerate() {
        let inner = if k == 0 {
            part
        } else {
            let Formula::BvShl(inner, amount, 64) = part else { return false };
            if !matches!(&**amount,Formula::BitVec{value,width:64}if *value==(k*8)as i128) {
                return false;
            }
            inner
        };
        let Formula::BvZeroExt(value, 56) = inner else { return false };
        if **value
            != (Formula::BvExtract {
                inner: Box::new(source.clone()),
                high: (k * 8 + 7) as u32,
                low: (k * 8) as u32,
            })
        {
            return false;
        }
    }
    true
}
fn chunks<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    if let Formula::BvOr(a, b, 64) = f {
        chunks(a, out);
        out.push(b);
    } else {
        out.push(f);
    }
}
fn read(f: &Formula, k: usize) -> Option<(&Formula, &Formula)> {
    let inner = if k == 0 {
        f
    } else {
        let Formula::BvShl(v, amount, 64) = f else { return None };
        if !matches!(&**amount,Formula::BitVec{value,width:64}if *value==(k*8)as i128) {
            return None;
        }
        v
    };
    let Formula::BvZeroExt(v, 56) = inner else { return None };
    let Formula::Select(memory, query) = &**v else { return None };
    Some((memory, query))
}
pub(super) fn instance(f: &Formula, c: &mut Context) -> Option<(Formula, Expr)> {
    if !c.frame_model {
        return None;
    }
    let mut parts = Vec::new();
    chunks(f, &mut parts);
    let count = parts.len();
    if !(1..=8).contains(&count) {
        return None;
    }
    let (memory, query) = read(parts[0], 0)?;
    let (start, values, args) = frame_reads::bindings(memory, query, c)?;
    if start != 0 && start != 8 {
        return None;
    }
    let (base, _) = frame::address(query)?;
    let mut normal = None;
    for (k, part) in parts.into_iter().enumerate() {
        let (m, q) = read(part, k)?;
        let (b, chain) = frame::address(q)?;
        if m != memory || b != base || chain != frame_offset_model::chain(start + k)? {
            return None;
        }
        let mut term = Formula::BvZeroExt(Box::new(values[start + k].clone()), 56);
        if k > 0 {
            term = Formula::BvShl(
                Box::new(term),
                Box::new(Formula::BitVec { value: (k * 8) as i128, width: 64 }),
                64,
            );
        }
        normal = Some(match normal {
            None => term,
            Some(prior) => Formula::BvOr(Box::new(prior), Box::new(term), 64),
        });
    }
    Some((normal?, Expr::apps(Expr::const_str(&frame_word_model::name(start / 8, count)), args)))
}
