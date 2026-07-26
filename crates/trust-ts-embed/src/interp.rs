//! A reference interpreter for `TsCore` — the executable side of the embedding.
//!
//! This is the foundation of `TS_EMBED_REFL`: running this interpreter on a corpus
//! and diffing against the *real* TypeScript executed in Node is the falsifiable
//! check that the embedding means what the TS actually does. It is also the
//! differential-execution witness that complements the deductive refinement proof
//! (the two-witness gate), and the oracle that makes mutation coverage measurable
//! (a behavior-changing mutant must diverge here).
//!
//! Integer results are width-masked to match the bitvector semantics the
//! `VerifiableFunction` lowering uses, so the interpreter and the lowered image
//! agree by construction on the in-fragment operations.

use std::collections::HashMap;

use trust_types::BinOp;

use crate::core::{TsExpr, TsFunction, TsStmt, TsTy};

/// The interpreter environment: scalar bindings, fixed-length array bindings, and
/// the in-module function table (for interprocedural calls).
struct Env {
    scalars: HashMap<String, i128>,
    arrays: HashMap<String, Vec<i128>>,
    funcs: HashMap<String, TsFunction>,
}

/// Evaluate `f` on the given named integer arguments. Returns the (width-masked)
/// result, or `None` if a variable is unbound, the body has no `return`, or an
/// unsupported operator is reached (fail-closed, never a wrong answer).
#[must_use]
pub fn eval(f: &TsFunction, args: &[(&str, i128)]) -> Option<i128> {
    eval_with_arrays(f, args, &[])
}

/// As [`eval`], with fixed-length array arguments (for array-reducer functions).
#[must_use]
pub fn eval_with_arrays(
    f: &TsFunction,
    scalars: &[(&str, i128)],
    arrays: &[(&str, &[i128])],
) -> Option<i128> {
    let mut env = Env {
        scalars: scalars.iter().map(|(n, v)| ((*n).to_string(), *v)).collect(),
        arrays: arrays.iter().map(|(n, v)| ((*n).to_string(), v.to_vec())).collect(),
        funcs: HashMap::new(),
    };
    for stmt in &f.body {
        match exec_stmt(stmt, &mut env)? {
            Flow::Return(v) => return Some(v),
            Flow::Next => {}
        }
    }
    None
}

/// Evaluate `entry` within a MODULE of functions (so calls to sibling functions
/// resolve). Returns the (width-masked) result, or `None` (fail-closed).
#[must_use]
pub fn eval_module(
    funcs: &[TsFunction],
    entry: &str,
    scalars: &[(&str, i128)],
    arrays: &[(&str, &[i128])],
) -> Option<i128> {
    let table: HashMap<String, TsFunction> =
        funcs.iter().map(|f| (f.name.clone(), f.clone())).collect();
    let f = table.get(entry)?;
    let mut env = Env {
        scalars: scalars.iter().map(|(n, v)| ((*n).to_string(), *v)).collect(),
        arrays: arrays.iter().map(|(n, v)| ((*n).to_string(), v.to_vec())).collect(),
        funcs: table.clone(),
    };
    for stmt in &f.body {
        match exec_stmt(stmt, &mut env)? {
            Flow::Return(v) => return Some(v),
            Flow::Next => {}
        }
    }
    None
}

/// Control flow from executing one statement.
enum Flow {
    Next,
    Return(i128),
}

/// Execute one statement, mutating `env`. `None` is a fail-closed evaluation error.
fn exec_stmt(s: &TsStmt, env: &mut Env) -> Option<Flow> {
    match s {
        TsStmt::Assign { var, value } => {
            let v = eval_expr(value, env)?;
            env.scalars.insert(var.name.clone(), v);
            Some(Flow::Next)
        }
        TsStmt::Return { value } => Some(Flow::Return(eval_expr(value, env)?)),
        TsStmt::ForRange { var, count, body } => {
            for k in 0..*count {
                env.scalars.insert(var.clone(), i128::from(k));
                for stmt in body {
                    if let Flow::Return(v) = exec_stmt(stmt, env)? {
                        return Some(Flow::Return(v));
                    }
                }
            }
            Some(Flow::Next)
        }
    }
}

fn eval_expr(e: &TsExpr, env: &Env) -> Option<i128> {
    match e {
        TsExpr::Int(v, _) => Some(*v),
        TsExpr::Bool(b) => Some(i128::from(*b)),
        TsExpr::Var(v) => env.scalars.get(&v.name).copied(),
        TsExpr::Bin { op, lhs, rhs, ty } => {
            let l = eval_expr(lhs, env)?;
            let r = eval_expr(rhs, env)?;
            eval_binop(*op, l, r, *ty)
        }
        TsExpr::If { cond, then_e, else_e, .. } => {
            let c = eval_expr(cond, env)?;
            if c != 0 { eval_expr(then_e, env) } else { eval_expr(else_e, env) }
        }
        TsExpr::Index { base, elem_width, index } => {
            let v = *env.arrays.get(base)?.get(*index as usize)?;
            Some(mask(v, TsTy::uint(*elem_width)))
        }
        TsExpr::IndexVar { base, elem_width, index_var } => {
            let i = *env.scalars.get(index_var)?;
            let v = *env.arrays.get(base)?.get(usize::try_from(i).ok()?)?;
            Some(mask(v, TsTy::uint(*elem_width)))
        }
        TsExpr::Field { obj, field, elem_width } => {
            let v = *env.scalars.get(&format!("{obj}.{field}"))?;
            Some(mask(v, TsTy::uint(*elem_width)))
        }
        TsExpr::IndexExpr { base, elem_width, index } => {
            let i = eval_expr(index, env)?;
            let v = *env.arrays.get(base)?.get(usize::try_from(i).ok()?)?;
            Some(mask(v, TsTy::uint(*elem_width)))
        }
        TsExpr::Call { func, args } => {
            let callee = env.funcs.get(func)?.clone();
            if args.len() != callee.params.len() {
                return None;
            }
            let argvals: Vec<i128> = args.iter().map(|a| eval_expr(a, env)).collect::<Option<_>>()?;
            let mut sub = Env {
                scalars: callee
                    .params
                    .iter()
                    .zip(&argvals)
                    .map(|(p, v)| (p.name.clone(), *v))
                    .collect(),
                arrays: env.arrays.clone(),
                funcs: env.funcs.clone(),
            };
            for stmt in &callee.body {
                if let Flow::Return(v) = exec_stmt(stmt, &mut sub)? {
                    return Some(v);
                }
            }
            None
        }
    }
}

fn eval_binop(op: BinOp, l: i128, r: i128, ty: TsTy) -> Option<i128> {
    let res = match op {
        BinOp::Add => l + r,
        BinOp::Sub => l - r,
        BinOp::Mul => l * r,
        BinOp::Lt => i128::from(l < r),
        BinOp::Le => i128::from(l <= r),
        BinOp::Gt => i128::from(l > r),
        BinOp::Ge => i128::from(l >= r),
        BinOp::Eq => i128::from(l == r),
        BinOp::Ne => i128::from(l != r),
        // On Bool operands these are LOGICAL connectives (matching the Bool-aware
        // lowering in vc_core): nonzero is true.
        BinOp::BitAnd => i128::from((l != 0) && (r != 0)),
        BinOp::BitOr => i128::from((l != 0) || (r != 0)),
        _ => return None,
    };
    Some(mask(res, ty))
}

/// Wrap an arithmetic result into the declared width: modular 2^width for unsigned,
/// two's-complement for signed, matching the lowered bitvector semantics. Bool and
/// width-128 pass through.
fn mask(v: i128, ty: TsTy) -> i128 {
    match ty {
        TsTy::Num { width, signed: false } if width < 128 => v & ((1i128 << width) - 1),
        TsTy::Num { width, signed: true } if width < 128 => {
            let m = 1i128 << width;
            let x = v & (m - 1);
            if x >= (1i128 << (width - 1)) { x - m } else { x }
        }
        _ => v,
    }
}
