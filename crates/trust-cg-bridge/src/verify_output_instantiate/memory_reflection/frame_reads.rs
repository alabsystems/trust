//! Restore/check fixed universal proofs, then instantiate the COMPLETE actual
//! entry array, all sixteen original stored values and unrestricted SP bits.
use super::*;
use crate::original_conjunction_certificate::TermPacket;
pub(super) fn install(env: &mut clean_kernel::Environment) -> Result<(), String> {
    let packets: Vec<TermPacket> = serde_json::from_slice(include_bytes!("frame_bank/reads.json"))
        .map_err(|e| e.to_string())?;
    if packets.len() != 16 {
        return Err("fixed frame-read theorem population".into());
    }
    for (q, packet) in packets.into_iter().enumerate() {
        let (goal, proof) = packet.restore()?;
        let expected = frame_read_model::statement(q).ok_or("invalid frame-read query")?;
        if goal != expected {
            return Err("fixed frame-read complete original statement mismatch".into());
        }
        clean_kernel::TypeChecker::with_mode(env, env.mode())
            .check_type(&proof, &expected)
            .map_err(|e| format!("fixed frame-read kernel refusal: {e:?}"))?;
        let name = Name::from_string(&frame_read_model::name(q));
        env.add_decl(clean_kernel::Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: expected,
            value: proof,
        })
        .map_err(|e| format!("fixed frame-read insertion: {e:?}"))?;
        if !env.axiom_deps(&name).ok_or("fixed frame-read closure unavailable")?.is_empty() {
            return Err("fixed frame-read logical axiom dependency".into());
        }
    }
    frame_words::install(env)
}
pub(super) fn bindings(
    memory: &Formula,
    query: &Formula,
    c: &mut Context,
) -> Option<(usize, Vec<Formula>, Vec<Expr>)> {
    if !c.frame_model {
        return None;
    }
    let (base, chain) = frame::address(query)?;
    let q = frame_offset_model::index(&chain)?;
    let mut current = memory;
    let mut stores = Vec::with_capacity(16);
    for _ in 0..16 {
        let Formula::Store(previous, address, value) = current else { return None };
        stores.push((&**address, &**value));
        current = previous;
    }
    // The entry memory may itself contain stores; every one is retained in the
    // actual array argument. Only the exact outer sixteen-store grid is matched.
    stores.reverse();
    for (i, (address, _)) in stores.iter().enumerate() {
        let (b, chain) = frame::address(address)?;
        if b != base || chain != frame_offset_model::chain(i)? {
            return None;
        }
    }
    let mut args = frame::bits64(&base, c)?.to_vec();
    args.push(original_memory(current, c)?);
    for (_, value) in &stores {
        args.push(frame::val(value, c)?);
    }
    Some((q, stores.iter().map(|(_, value)| (*value).clone()).collect(), args))
}
pub(super) fn instance(
    memory: &Formula,
    query: &Formula,
    c: &mut Context,
) -> Option<(Formula, Expr)> {
    let (q, values, args) = bindings(memory, query, c)?;
    Some((values[q].clone(), Expr::apps(Expr::const_str(&frame_read_model::name(q)), args)))
}
