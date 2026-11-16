//! Proof-only restoration of ORIGINAL frame equations. No folded ABI assertion.
use scalar_bits::Bit;

use super::*;
pub(super) fn val(f: &Formula, c: &mut Context) -> Option<Expr> {
    Some(kx::evalf(original_value(f, c)?))
}
fn boxed(f: Formula) -> Box<Formula> {
    Box::new(f)
}
pub(super) fn has_shift(f: &Formula) -> bool {
    match f {
        Formula::BvShl(..) => true,
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvConcat(a, b)
        | Formula::Select(a, b) => has_shift(a) || has_shift(b),
        Formula::BvZeroExt(a, _)
        | Formula::BvSignExt(a, _)
        | Formula::BvNot(a, _)
        | Formula::BvExtract { inner: a, .. } => has_shift(a),
        Formula::Store(a, b, v) | Formula::Ite(a, b, v) => {
            has_shift(a) || has_shift(b) || has_shift(v)
        }
        _ => false,
    }
}
fn has_read(f: &Formula) -> bool {
    match f {
        Formula::Select(..) => true,
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvConcat(a, b) => has_read(a) || has_read(b),
        Formula::BvZeroExt(a, _)
        | Formula::BvSignExt(a, _)
        | Formula::BvNot(a, _)
        | Formula::BvExtract { inner: a, .. } => has_read(a),
        Formula::Store(a, b, v) | Formula::Ite(a, b, v) => {
            has_read(a) || has_read(b) || has_read(v)
        }
        _ => false,
    }
}
pub(super) fn bits64(f: &Formula, c: &mut Context) -> Option<[Expr; 64]> {
    scalar_bits::frame_bits(f, c)?.iter().map(scalar_bits::expr).collect::<Vec<_>>().try_into().ok()
}
pub(super) fn address(f: &Formula) -> Option<(Formula, Vec<i128>)> {
    match f {
        Formula::Var(_, Sort::BitVec(64)) => Some((f.clone(), vec![])),
        Formula::BvAdd(a, b, 64) => {
            let Formula::BitVec { value, width: 64 } = &**b else { return None };
            let (base, mut xs) = address(a)?;
            xs.push(*value);
            Some((base, xs))
        }
        _ => None,
    }
}
fn different(a: &Formula, b: &Formula, c: &mut Context) -> Option<Expr> {
    let (av, aa) = address(a)?;
    let (bv, bb) = address(b)?;
    if av != bv {
        return None;
    }
    let bits = bits64(&av, c)?;
    if let Some(proof) = frame_offsets::instance(&bits, &aa, &bb) {
        return Some(proof);
    }
    frame_arithmetic::distinct_offsets(&bits, &aa, &bb)
}
fn restored_read(memory: &Formula, query: &Formula, c: &mut Context) -> Option<(Formula, Expr)> {
    if let Some(result) = frame_reads::instance(memory, query, c) {
        return Some(result);
    }
    let Formula::Store(previous, address, value) = memory else { return None };
    let before = Formula::Select(boxed(memory.clone()), boxed(query.clone()));
    let previous_value = original_memory(previous, c)?;
    let av = val(address, c)?;
    let qv = val(query, c)?;
    let vv = val(value, c)?;
    if **address == *query {
        return Some(((**value).clone(), kx::select_store_same(previous_value, av, vv)));
    }
    let guard = different(address, query, c)?;
    let first = Expr::apps(
        Expr::const_str("Clean.BVC.selectStoreDiff"),
        [previous_value, av, qv, vv, guard],
    );
    let after = Formula::Select(previous.clone(), boxed(query.clone()));
    let (target, second) = restored_read(previous, query, c)?;
    let proof =
        trans(kx::list_bool(), val(&before, c)?, val(&after, c)?, val(&target, c)?, first, second);
    Some((target, proof))
}
fn operation(f: &Formula, args: &[Expr]) -> Option<Expr> {
    match f {
        Formula::BvOr(..) => {
            Some(Expr::apps(Expr::const_str("Clean.BVC.bvZipOr"), args.iter().cloned()))
        }
        Formula::BvShl(..) => {
            Some(Expr::apps(Expr::const_str("Clean.BVC.bvShl"), args.iter().cloned()))
        }
        Formula::BvZeroExt(_, n) => Some(Expr::apps(
            Expr::const_str("Clean.BVC.bvZeroExt"),
            [args[0].clone(), kx::nat_lit(*n)],
        )),
        _ => None,
    }
}
fn operands(f: &Formula) -> Option<Vec<Formula>> {
    match f {
        Formula::BvOr(a, b, _) | Formula::BvShl(a, b, _) => {
            Some(vec![(**a).clone(), (**b).clone()])
        }
        Formula::BvZeroExt(a, _) => Some(vec![(**a).clone()]),
        _ => None,
    }
}
fn rebuild(f: &Formula, args: &[Formula]) -> Option<Formula> {
    match f {
        Formula::BvOr(_, _, w) => {
            Some(Formula::BvOr(boxed(args[0].clone()), boxed(args[1].clone()), *w))
        }
        Formula::BvShl(_, _, w) => {
            Some(Formula::BvShl(boxed(args[0].clone()), boxed(args[1].clone()), *w))
        }
        Formula::BvZeroExt(_, n) => Some(Formula::BvZeroExt(boxed(args[0].clone()), *n)),
        _ => None,
    }
}
/// Transport every child equality through the ACTUAL semantic operation.
fn congr_children(f: &Formula, old: &[Expr], new: &[Expr], proofs: &[Expr]) -> Option<Expr> {
    if matches!(f, Formula::BvOr(..)) && old.len() == 2 && new.len() == 2 && proofs.len() == 2 {
        return Some(kx::or_cong(
            kx::leaf(old[0].clone()),
            kx::leaf(new[0].clone()),
            kx::leaf(old[1].clone()),
            kx::leaf(new[1].clone()),
            proofs[0].clone(),
            proofs[1].clone(),
        ));
    }
    let mut current = old.to_vec();
    let original = operation(f, &current)?;
    let mut p = refl(kx::list_bool(), original.clone());
    for i in 0..old.len() {
        let before = operation(f, &current)?;
        let mut target = current.clone();
        target[i] = new[i].clone();
        let after = operation(f, &target)?;
        let mut body = current.clone();
        body[i] = Expr::bvar(0);
        let step = congr(
            kx::list_bool(),
            kx::list_bool(),
            old[i].clone(),
            new[i].clone(),
            lam(kx::list_bool(), operation(f, &body)?),
            proofs[i].clone(),
        );
        p = trans(kx::list_bool(), original.clone(), before, after, p, step);
        current = target;
    }
    Some(p)
}
fn normalize_reads(f: &Formula, c: &mut Context) -> Option<(Formula, Expr)> {
    if !has_read(f) {
        return Some((f.clone(), refl(kx::list_bool(), val(f, c)?)));
    }
    if let Some(result) = frame_words::instance(f, c) {
        return Some(result);
    }
    if let Formula::Select(memory, query) = f {
        return restored_read(memory, query, c);
    }
    let old = operands(f)?;
    let mut new = Vec::new();
    let mut proofs = Vec::new();
    for x in &old {
        let (y, p) = normalize_reads(x, c)?;
        new.push(y);
        proofs.push(p)
    }
    let before = old.iter().map(|x| val(x, c)).collect::<Option<Vec<_>>>()?;
    let after = new.iter().map(|x| val(x, c)).collect::<Option<Vec<_>>>()?;
    Some((rebuild(f, &new)?, congr_children(f, &before, &after, &proofs)?))
}
fn scalar_bridge(f: &Formula, c: &mut Context) -> Option<(Vec<Bit>, Expr)> {
    let bits = scalar_bits::frame_bits(f, c)?;
    if !has_shift(f) {
        let value = scalar_bits::list(&bits);
        return Some((bits, refl(kx::list_bool(), value)));
    }
    if let Formula::BvShl(inner, amount, 64) = f {
        let Formula::BvZeroExt(byte, 56) = &**inner else { return None };
        if width(byte)? != 8 {
            return None;
        }
        let Formula::BitVec { value, width: 64 } = &**amount else { return None };
        let k = u32::try_from(*value).ok()?;
        let byte = scalar_bits::frame_bits(byte, c)?;
        let values = byte.iter().map(scalar_bits::expr).collect::<Vec<_>>();
        return Some((bits, frame_bank::instance(k, &values)?));
    }
    let children = operands(f)?;
    let mut old = Vec::new();
    let mut new = Vec::new();
    let mut proofs = Vec::new();
    for x in children {
        old.push(val(&x, c)?);
        let (b, p) = scalar_bridge(&x, c)?;
        new.push(scalar_bits::list(&b));
        proofs.push(p)
    }
    Some((bits, congr_children(f, &old, &new, &proofs)?))
}
fn stack_proof(a: &Formula, b: &Formula, c: &mut Context) -> Option<Expr> {
    let Formula::Var(_, Sort::BitVec(64)) = b else { return None };
    let Formula::BvAdd(inner, last, 64) = a else { return None };
    if !matches!(&**last, Formula::BitVec { value: 16, width: 64 }) {
        return None;
    }
    match &**inner {
        Formula::BvAdd(base, negative, 64)
            if **base == *b && matches!(&**negative, Formula::BitVec { value: -16, width: 64 }) =>
        {
            Some(frame_arithmetic::restore_sp(&bits64(b, c)?))
        }
        Formula::BvSub(base, positive, 64)
            if **base == *b && matches!(&**positive, Formula::BitVec { value: 16, width: 64 }) =>
        {
            Some(frame_arithmetic::restore_sp_sub(&bits64(b, c)?))
        }
        _ => None,
    }
}
pub(super) fn equation(
    machine: &Formula,
    source: &Formula,
    c: &mut Context,
) -> Option<(Expr, Expr, Expr, Expr)> {
    #[cfg(any(test, feature = "test-hooks"))]
    crate::original_conjunction_certificate::require_production_allowed();
    let left = val(machine, c)?;
    let right = val(source, c)?;
    let goal = equality(kx::list_bool(), left.clone(), right.clone());
    if let Some(proof) = stack_proof(machine, source, c) {
        return Some((goal, proof, left, right));
    }
    if !c.frame_model || !has_read(machine) {
        return None;
    }
    let (normal, reads) = normalize_reads(machine, c)?;
    let normal_value = val(&normal, c)?;
    if matches!(source, Formula::Var(_, Sort::BitVec(64)))
        && frame_words::reassembles_from(&normal, source)
    {
        let assembly = frame_assembly::instance(&bits64(source, c)?);
        let proof =
            trans(kx::list_bool(), left.clone(), normal_value, right.clone(), reads, assembly);
        return Some((goal, proof, left, right));
    }
    let (mbits, mp) = scalar_bridge(&normal, c)?;
    let (sbits, sp) = scalar_bridge(source, c)?;
    let mv = scalar_bits::list(&mbits);
    let sv = scalar_bits::list(&sbits);
    let bit_proof = scalar_bits::prove_bits(&mbits, &sbits)?;
    let reverse = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [kx::list_bool(), right.clone(), sv.clone(), sp],
    );
    let last = trans(kx::list_bool(), mv.clone(), sv, right.clone(), bit_proof, reverse);
    let mid = trans(kx::list_bool(), normal_value.clone(), mv, right.clone(), mp, last);
    let proof = trans(kx::list_bool(), left.clone(), normal_value, right.clone(), reads, mid);
    Some((goal, proof, left, right))
}
