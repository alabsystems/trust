// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! TG11's closed, by-value ODT reader. This reads values, never layout or
//! references. It grants no B1 standing: the importer must bind every nominal
//! parameter to a separately checked ODT face before producing a kernel term.
use crate::{
    BinOp, ConstValue, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Leaf {
    Param(usize),
    Field { param: usize, field: usize },
    Bool(bool),
    Int(i128),
}

#[derive(Clone, Debug)]
pub enum Body {
    Projection(Leaf),
    /// Branches are in Rust declaration order, never sorted by discriminant.
    Cases {
        param: usize,
        branches: Vec<Leaf>,
    },
}

pub fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool | Ty::Int { width: 8 | 16 | 32 | 64, .. })
}

fn enum_tags(ty: &Ty) -> Option<Vec<i128>> {
    let Ty::Adt { variants, adt_kind, .. } = ty else { return None };
    if adt_kind.is_some_and(|k| k != crate::AdtKind::Enum) {
        return None;
    }
    if variants.is_empty() || variants.len() > 256 {
        return None;
    }
    let mut seen_bits = [0u64; 4];
    let mut tags = Vec::with_capacity(variants.len());
    for v in variants.iter() {
        if !v.fields.is_empty() || !(0..=255).contains(&v.discriminant) {
            return None;
        }
        let disc = v.discriminant as usize;
        let word = &mut seen_bits[disc >> 6];
        let mask = 1u64 << (disc & 63);
        if *word & mask != 0 {
            return None;
        }
        *word |= mask;
        tags.push(v.discriminant);
    }
    Some(tags)
}

fn fields(ty: &Ty) -> Option<&[(String, Ty)]> {
    let Ty::Adt { fields, variants, adt_kind, .. } = ty else { return None };
    if adt_kind.is_some_and(|k| k != crate::AdtKind::Struct) {
        return None;
    }
    (variants.is_empty() && !fields.is_empty() && fields.iter().all(|(_, t)| scalar(t)))
        .then_some(fields.as_slice())
}

#[derive(Clone)]
enum Value {
    Leaf(Leaf, Ty),
    Enum(usize),
    Tag { param: usize, value: i128 },
}

/// Validate complete local/block identity and evaluate the closed fragment for
/// each constructor. A branch is a scalar leaf/projection; a second symbolic
/// branch (including a guard) is refused. No calls, drops, assertions, symbolic casts,
/// arithmetic, writes through projections or back edges are admitted.
pub fn read(func: &VerifiableFunction) -> Option<Body> {
    let body = &func.body;
    if !scalar(&body.return_ty)
        || body.locals.len() <= body.arg_count
        || body.blocks.is_empty()
        || body.blocks.len() > 1024
    {
        return None;
    }
    if body.locals.iter().enumerate().any(|(i, l)| l.index != i)
        || body.blocks.iter().enumerate().any(|(i, b)| b.id.0 != i)
    {
        return None;
    }
    if body.locals[0].ty != body.return_ty {
        return None;
    }
    let params = &body.locals[1..=body.arg_count];
    let mut enum_param = None;
    let mut tags = vec![0];
    let mut has_odt = false;
    for (i, p) in params.iter().enumerate() {
        if let Some(ts) = enum_tags(&p.ty) {
            if enum_param.replace(i).is_some() {
                return None;
            }
            tags = ts;
            has_odt = true;
        } else if fields(&p.ty).is_some() {
            has_odt = true;
        } else if !scalar(&p.ty) {
            return None;
        }
    }
    if !has_odt {
        return None;
    }
    for l in body.locals.iter().skip(body.arg_count + 1) {
        if !scalar(&l.ty) && !matches!(l.ty, Ty::PtrSizedInt { .. }) {
            return None;
        }
    }
    // Check even dead blocks for unsupported effects and dangling edges.
    for b in &body.blocks {
        for s in &b.stmts {
            match s {
                Statement::Assign { place, rvalue, .. }
                    if place.projections.is_empty()
                        && place.local < body.locals.len()
                        && (place.local == 0 || place.local > body.arg_count) =>
                {
                    if !matches!(
                        rvalue,
                        Rvalue::Use(_)
                            | Rvalue::Discriminant(_)
                            | Rvalue::Cast(..)
                            | Rvalue::BinaryOp(BinOp::Eq | BinOp::Ne, ..)
                    ) {
                        return None;
                    }
                }
                Statement::StorageLive(i) | Statement::StorageDead(i)
                    if *i > body.arg_count && *i < body.locals.len() => {}
                Statement::Nop | Statement::Coverage | Statement::ConstEvalCounter => {}
                _ => return None,
            }
        }
        match &b.terminator {
            Terminator::Return | Terminator::Unreachable => {}
            Terminator::Goto(t) if t.0 < body.blocks.len() => {}
            Terminator::SwitchInt { targets, otherwise, .. }
                if otherwise.0 < body.blocks.len()
                    && targets.iter().all(|(_, t)| t.0 < body.blocks.len())
                    && (if targets.len() <= 16 {
                        targets.iter().enumerate().all(|(idx, (v, _))| {
                            !targets[..idx].iter().any(|(prev, _)| prev == v)
                        })
                    } else {
                        let mut seen = crate::fx::FxHashSet::with_capacity_and_hasher(
                            targets.len(),
                            Default::default(),
                        );
                        targets.iter().all(|(v, _)| seen.insert(*v))
                    }) => {}
            _ => return None,
        }
    }
    let place_value = |p: &Place, state: &[Option<Value>]| -> Option<Value> {
        if p.projections.is_empty() {
            return state.get(p.local)?.clone();
        }
        let [Projection::Field(field)] = p.projections.as_slice() else { return None };
        let param = p.local.checked_sub(1)?;
        let (_, ty) = fields(&params.get(param)?.ty)?.get(*field)?;
        Some(Value::Leaf(Leaf::Field { param, field: *field }, ty.clone()))
    };
    let operand = |op: &Operand, state: &[Option<Value>]| -> Option<Value> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => place_value(p, state),
            Operand::Constant(ConstValue::Bool(b)) => Some(Value::Leaf(Leaf::Bool(*b), Ty::Bool)),
            Operand::Constant(ConstValue::Int(n)) => {
                let Ty::Int { width, signed: true } = body.return_ty else { return None };
                if *n < -(1i128 << (width - 1)) || *n >= (1i128 << (width - 1)) {
                    return None;
                }
                Some(Value::Leaf(Leaf::Int(*n), body.return_ty.clone()))
            }
            Operand::Constant(ConstValue::Uint(n, w))
                if matches!(*w, 8 | 16 | 32 | 64) && *n < (1u128 << w) =>
            {
                Some(Value::Leaf(
                    Leaf::Int(i128::try_from(*n).ok()?),
                    Ty::Int { width: *w, signed: false },
                ))
            }
            _ => None,
        }
    };
    let mut branches = Vec::with_capacity(tags.len());
    let mut state = vec![None; body.locals.len()];
    for tag in tags {
        state.fill(None);
        for (i, p) in params.iter().enumerate() {
            state[i + 1] = if Some(i) == enum_param {
                Some(Value::Enum(i))
            } else if scalar(&p.ty) {
                Some(Value::Leaf(Leaf::Param(i), p.ty.clone()))
            } else {
                None
            };
        }
        // `body.blocks.len() <= 1024`, so 16 words of 64 bits track visited blocks on the stack.
        let mut seen = [0u64; 16];
        let mut block = 0;
        loop {
            let word = &mut seen[block >> 6];
            let mask = 1u64 << (block & 63);
            if *word & mask != 0 {
                return None;
            }
            *word |= mask;
            let b = &body.blocks[block];
            for s in &b.stmts {
                match s {
                    Statement::Assign { place, rvalue, .. } => {
                        let value = match rvalue {
                            Rvalue::Use(op) => operand(op, &state)?,
                            Rvalue::Discriminant(p) => {
                                let Value::Enum(param) = place_value(p, &state)? else {
                                    return None;
                                };
                                Value::Tag { param, value: tag }
                            }
                            // SimplifyMatch can turn enum arms 0/1 into a
                            // concrete boolean cast, or preserve only a tag
                            // cast. Symbolic casts remain outside E6.
                            Rvalue::Cast(op, target) => {
                                if !scalar(target) {
                                    return None;
                                }
                                let value = match operand(op, &state)? {
                                    Value::Leaf(Leaf::Bool(b), Ty::Bool) => i128::from(b),
                                    Value::Tag { value, .. } => value,
                                    _ => return None,
                                };
                                let Ty::Int { width, signed } = target else {
                                    return None;
                                };
                                let modulus = 1i128 << width;
                                let raw = value.rem_euclid(modulus);
                                let decoded =
                                    if *signed && raw >= modulus / 2 { raw - modulus } else { raw };
                                Value::Leaf(Leaf::Int(decoded), target.clone())
                            }
                            // MIR can if-convert a two-arm enum match into a
                            // discriminant equality. Evaluate that equality at
                            // each actual constructor, still emitting casesOn.
                            Rvalue::BinaryOp(op @ (BinOp::Eq | BinOp::Ne), l, r) => {
                                let (a, b) = (operand(l, &state)?, operand(r, &state)?);
                                let eq = match (a, b) {
                                    (
                                        Value::Tag { value, .. },
                                        Value::Leaf(
                                            Leaf::Int(n),
                                            Ty::Int { width: 8, signed: false },
                                        ),
                                    )
                                    | (
                                        Value::Leaf(
                                            Leaf::Int(n),
                                            Ty::Int { width: 8, signed: false },
                                        ),
                                        Value::Tag { value, .. },
                                    ) => value == n,
                                    _ => return None,
                                };
                                Value::Leaf(
                                    Leaf::Bool(if *op == BinOp::Eq { eq } else { !eq }),
                                    Ty::Bool,
                                )
                            }
                            _ => return None,
                        };
                        match &value {
                            Value::Leaf(_, ty) if *ty == body.locals[place.local].ty => {}
                            Value::Tag { .. }
                                if matches!(
                                    body.locals[place.local].ty,
                                    Ty::Int { width: 8, signed: false }
                                ) => {}
                            _ => return None,
                        }
                        state[place.local] = Some(value);
                    }
                    Statement::StorageLive(i) | Statement::StorageDead(i) => state[*i] = None,
                    _ => {}
                }
            }
            match &b.terminator {
                Terminator::Goto(t) => block = t.0,
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    let value = match operand(discr, &state)? {
                        Value::Tag { param, value } if Some(param) == enum_param => value,
                        _ => return None,
                    };
                    block = targets
                        .iter()
                        .find(|(v, _)| *v == value as u128)
                        .map_or(otherwise.0, |(_, t)| t.0);
                }
                Terminator::Return => {
                    let (leaf, ty) = match state[0].clone()? {
                        Value::Leaf(leaf, ty) => (leaf, ty),
                        Value::Tag { param, value } if Some(param) == enum_param => {
                            (Leaf::Int(value), Ty::Int { width: 8, signed: false })
                        }
                        _ => return None,
                    };
                    if ty != body.return_ty {
                        return None;
                    }
                    branches.push(leaf);
                    break;
                }
                _ => return None,
            }
        }
    }
    Some(match enum_param {
        Some(param) => Body::Cases { param, branches },
        None => Body::Projection(branches.pop()?),
    })
}

#[cfg(test)]
mod tests;
