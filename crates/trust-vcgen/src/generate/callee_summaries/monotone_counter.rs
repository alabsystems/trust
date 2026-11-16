//! Monotone bounds require the successful checked-arithmetic edge at each read.
//! The bound is global, so one pre-assert or bypassing definition declines it.

use trust_types::{
    AssertMessage, BinOp, ConstValue, Operand, Projection, Rvalue, Terminator, Ty,
    VerifiableFunction,
};

use super::operand_const_int;

#[derive(Clone, Copy, PartialEq)]
enum Side {
    Lower,
    Upper,
}

pub(super) fn bounds(func: &VerifiableFunction, local: usize) -> (Option<i128>, Option<i128>) {
    let side = |s| bound(func, local, s, 8, &mut Vec::new()).ok().flatten();
    (side(Side::Lower), side(Side::Upper))
}

/// `Ok(None)` is a monotone cycle contribution, not admission of an unknown write.
fn bound(
    func: &VerifiableFunction,
    local: usize,
    side: Side,
    fuel: u32,
    stack: &mut Vec<usize>,
) -> Result<Option<i128>, ()> {
    if stack.contains(&local) {
        return Ok(None);
    }
    if fuel == 0 {
        return Err(());
    }
    if let Some((Some(start), end)) = super::super::loop_bounds::loop_var_const_range(func, local) {
        if start >= end {
            return Err(());
        }
        return Ok(Some(if side == Side::Lower { start } else { end - 1 }));
    }
    let defs = crate::local_defs::value_defs(func, local).ok_or(())?;
    if defs.is_empty() {
        return Err(());
    }
    stack.push(local);
    let mut acc: Option<i128> = None;
    for (read_block, rvalue) in defs {
        let contribution = match rvalue {
            Rvalue::Use(op @ Operand::Constant(_)) => Some(operand_const_int(op).ok_or(())?),
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                bound(func, p.local, side, fuel - 1, stack)?
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if p.projections.as_slice() == [trust_types::Projection::Field(0)] =>
            {
                let Some(Rvalue::CheckedBinaryOp(op, x, d)) =
                    crate::local_defs::unique_value_def(func, p.local)
                else {
                    return Err(());
                };
                // The result must be read after the successful overflow guard,
                // not merely defined in a block that later checks overflow.
                if !checked_result_types(func, local, p.local, x, d)
                    || !guarded_result_read(func, p.local, read_block)
                {
                    return Err(());
                }
                let d = operand_const_int(d).filter(|d| *d >= 0).ok_or(())?;
                let (Operand::Copy(xp) | Operand::Move(xp)) = x else {
                    return Err(());
                };
                if !xp.projections.is_empty() {
                    return Err(());
                }
                // The side's own monotone operation only; anything else refuses
                // BEFORE recursing, so a cycle can never excuse it.
                match (op, side) {
                    (BinOp::Add, Side::Lower) | (BinOp::Sub, Side::Upper) => {}
                    _ => return Err(()),
                }
                // Checked: a `u128` counter's bound can leave `i128`; decline.
                match bound(func, xp.local, side, fuel - 1, stack)? {
                    None => None,
                    Some(b) if side == Side::Lower => Some(b.checked_add(d).ok_or(())?),
                    Some(b) => Some(b.checked_sub(d).ok_or(())?),
                }
            }
            _ => return Err(()),
        };
        if let Some(b) = contribution {
            acc = Some(match (acc, side) {
                (None, _) => b,
                (Some(a), Side::Lower) => a.min(b),
                (Some(a), Side::Upper) => a.max(b),
            });
        }
    }
    stack.pop();
    Ok(acc)
}

/// The successful Assert edge must dominate this projection read. The unique
/// tuple definition has no partial writes or aliases, so its flag and result
/// still describe the same arithmetic operation at the read.
fn guarded_result_read(func: &VerifiableFunction, tuple: usize, read: usize) -> bool {
    let tp = super::super::terminator_presence_for(func);
    if !tp.has_assert || tp.has_opaque {
        return false;
    }
    let Some(def) = crate::local_defs::unique_defining_block(func, tuple) else {
        return false;
    };
    let Some(block) = func.body.blocks.get(def) else {
        return false;
    };
    let Terminator::Assert {
        cond: Operand::Copy(cond) | Operand::Move(cond),
        expected: false,
        target,
        msg: AssertMessage::Overflow(guard_op),
        ..
    } = &block.terminator
    else {
        return false;
    };
    let Some(Rvalue::CheckedBinaryOp(op, _, _)) = crate::local_defs::unique_value_def(func, tuple)
    else {
        return false;
    };
    if guard_op != op
        || cond.local != tuple
        || cond.projections.as_slice() != [Projection::Field(1)]
        || read == def
        || read >= func.body.blocks.len()
        || block.terminator.has_unguarded_successor(*target)
    {
        return false;
    }
    let n = func.body.blocks.len();
    if n > u32::MAX as usize {
        return false;
    }
    crate::fn_memo::count_body_scan_items(n as u64);
    for (i, b) in func.body.blocks.iter().enumerate() {
        if b.id.0 != i
            || !matches!(
                &b.terminator,
                Terminator::Goto(_)
                    | Terminator::SwitchInt { .. }
                    | Terminator::Call { .. }
                    | Terminator::Assert { .. }
                    | Terminator::Drop { .. }
                    | Terminator::Return
                    | Terminator::TailCall { .. }
                    | Terminator::Unreachable
                    | Terminator::Resume
            )
            || super::super::any_full_graph_terminator_target(&b.terminator, |t| t.0 >= n)
        {
            return false;
        }
    }
    if target.0 >= n {
        return false;
    }
    let versions = super::super::stmt_versions_for(func);
    let cfg = versions.cfg();
    let dom = cfg.dom();
    let (s, t) = (def as u32, target.0 as u32);
    // The existing dominating_facts::edge_dominates_target criterion, including
    // full unwind edges and back-edge predecessors. A cleanup edge to the same
    // target is rejected above as an unguarded parallel edge.
    dom.dominates(cfg.entry_def(), s)
        && s != t
        && !dom.dominates(t, s)
        && cfg
            .preds(t)
            .iter()
            .all(|&p| p == s || !dom.dominates(cfg.entry_def(), p) || dom.dominates(t, p))
        && dom.dominates(t, read as u32)
}

/// A public typed body must describe one consistent integer operation; the
/// dominance premise cannot repair a mismatched result or overflow flag type.
fn checked_result_types(
    func: &VerifiableFunction,
    destination: usize,
    tuple: usize,
    source: &Operand,
    delta: &Operand,
) -> bool {
    let (Some(dest), Some(tuple_ty)) = (local_ty(func, destination), local_ty(func, tuple)) else {
        return false;
    };
    let (Ty::Tuple(fields), Operand::Copy(src) | Operand::Move(src)) = (tuple_ty, source) else {
        return false;
    };
    if !matches!(dest, Ty::Int { .. } | Ty::PtrSizedInt { .. })
        || !matches!(fields.as_slice(), [result, Ty::Bool] if result == dest)
        || !src.projections.is_empty()
        || local_ty(func, src.local) != Some(dest)
    {
        return false;
    }
    let Some(width @ (8 | 16 | 32 | 64 | 128)) = dest.int_width() else {
        return false;
    };
    match delta {
        Operand::Constant(ConstValue::Uint(value, bits)) if !dest.is_signed() => {
            *bits == width && (width == 128 || *value < (1u128 << width))
        }
        Operand::Constant(ConstValue::Int(value)) if dest.is_signed() => {
            *value >= 0 && (width == 128 || *value < (1i128 << (width - 1)))
        }
        _ => false,
    }
}

fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    crate::unique_local_decl(func, local).map(|decl| &decl.ty)
}

#[cfg(test)]
mod tests;
