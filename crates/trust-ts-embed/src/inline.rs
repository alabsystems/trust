//! Interprocedural support by **inlining**: resolve calls to sibling functions so a
//! composed (multi-function) TypeScript program reduces to one call-free `TsCore`
//! image the denotational refinement can prove. Callees must be single-`return`-
//! expression helpers over scalar params (the common composition shape); anything
//! else fails closed as a [`FragmentEscape`] — never a silent partial inline.

use std::collections::HashMap;

use crate::core::{TsExpr, TsFunction, TsStmt};
use crate::escape::{FragmentEscape, UnsupportedTsConstruct};
use trust_types::BinOp;

/// Maximum call-inlining depth. Bounds BOUNDED recursion (a recursive call whose
/// argument is constant-folded down to its base case resolves within the limit);
/// unbounded / symbolically-deep recursion exceeds it and fails CLOSED — never an
/// infinite inline, never a silent truncation.
const MAX_INLINE_DEPTH: u32 = 64;

/// Inline every call in `entry` against the module's `funcs`, returning a call-free
/// `TsFunction`. Fails closed on unknown callees, arity mismatches, callees that are
/// not single-return-expression helpers, or recursion deeper than [`MAX_INLINE_DEPTH`].
pub fn inline_calls(entry: &TsFunction, funcs: &[TsFunction]) -> Result<TsFunction, FragmentEscape> {
    let table: HashMap<&str, &TsFunction> = funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    let body = entry
        .body
        .iter()
        .map(|s| inline_stmt(s, &table, &entry.name, 0))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TsFunction { body, ..entry.clone() })
}

fn inline_stmt(
    s: &TsStmt,
    table: &HashMap<&str, &TsFunction>,
    sym: &str,
    depth: u32,
) -> Result<TsStmt, FragmentEscape> {
    Ok(match s {
        TsStmt::Assign { var, value } => {
            TsStmt::Assign { var: var.clone(), value: inline_expr(value, table, sym, depth)? }
        }
        TsStmt::Return { value } => TsStmt::Return { value: inline_expr(value, table, sym, depth)? },
        TsStmt::ForRange { var, count, body } => TsStmt::ForRange {
            var: var.clone(),
            count: *count,
            body: body
                .iter()
                .map(|s| inline_stmt(s, table, sym, depth))
                .collect::<Result<_, _>>()?,
        },
    })
}

fn inline_expr(
    e: &TsExpr,
    table: &HashMap<&str, &TsFunction>,
    sym: &str,
    depth: u32,
) -> Result<TsExpr, FragmentEscape> {
    Ok(match e {
        TsExpr::Call { func, args } => {
            if depth >= MAX_INLINE_DEPTH {
                return Err(FragmentEscape::new(
                    sym,
                    UnsupportedTsConstruct::UnsupportedControlFlow {
                        kind: format!(
                            "recursion to `{func}` exceeds the {MAX_INLINE_DEPTH}-level inline \
                             bound (unbounded or symbolically-deep recursion)"
                        ),
                    },
                ));
            }
            let callee = table.get(func.as_str()).ok_or_else(|| {
                FragmentEscape::new(
                    sym,
                    UnsupportedTsConstruct::UnmodeledCall { callee: func.clone() },
                )
            })?;
            let ret = match callee.body.as_slice() {
                [TsStmt::Return { value }] => value,
                _ => {
                    return Err(FragmentEscape::new(
                        sym,
                        UnsupportedTsConstruct::UnsupportedControlFlow {
                            kind: format!(
                                "call to `{func}` (only single-return-expression helpers inline)"
                            ),
                        },
                    ));
                }
            };
            if args.len() != callee.params.len() {
                return Err(FragmentEscape::new(
                    sym,
                    UnsupportedTsConstruct::UnknownConstruct {
                        detail: format!("arity mismatch calling `{func}`"),
                    },
                ));
            }
            // Inline the argument expressions, bind them to the callee's params, and
            // substitute into the callee's return expression — then resolve any
            // nested calls it contains.
            let inlined_args = args
                .iter()
                .map(|a| inline_expr(a, table, sym, depth))
                .collect::<Result<Vec<_>, _>>()?;
            let pmap: HashMap<&str, TsExpr> = callee
                .params
                .iter()
                .map(|p| p.name.as_str())
                .zip(inlined_args)
                .collect();
            // Substitute, then CONSTANT-FOLD: for a recursive call with a constant-
            // bounded argument, the base-case guard folds and prunes the recursive
            // branch, so the recursion terminates within the depth bound.
            let substituted = fold(subst(ret, &pmap));
            inline_expr(&substituted, table, sym, depth + 1)?
        }
        TsExpr::Bin { op, lhs, rhs, ty } => TsExpr::Bin {
            op: *op,
            lhs: Box::new(inline_expr(lhs, table, sym, depth)?),
            rhs: Box::new(inline_expr(rhs, table, sym, depth)?),
            ty: *ty,
        },
        TsExpr::If { cond, then_e, else_e, ty } => TsExpr::If {
            cond: Box::new(inline_expr(cond, table, sym, depth)?),
            then_e: Box::new(inline_expr(then_e, table, sym, depth)?),
            else_e: Box::new(inline_expr(else_e, table, sym, depth)?),
            ty: *ty,
        },
        TsExpr::IndexExpr { base, elem_width, index } => TsExpr::IndexExpr {
            base: base.clone(),
            elem_width: *elem_width,
            index: Box::new(inline_expr(index, table, sym, depth)?),
        },
        // No nested calls possible: literals, vars, constant/var indexing, fields.
        other => other.clone(),
    })
}

/// Sound constant-folding: `Bin` over two integer literals folds to the literal
/// result (or Bool for a comparison), and an `If` with a constant condition folds
/// to the taken branch. Used during inlining so bounded recursion terminates.
fn fold(e: TsExpr) -> TsExpr {
    match e {
        TsExpr::Bin { op, lhs, rhs, ty } => {
            let (l, r) = (fold(*lhs), fold(*rhs));
            if let (TsExpr::Int(a, _), TsExpr::Int(b, _)) = (&l, &r) {
                let (a, b) = (*a, *b);
                return match op {
                    BinOp::Add => TsExpr::Int(a + b, ty),
                    BinOp::Sub => TsExpr::Int(a - b, ty),
                    BinOp::Mul => TsExpr::Int(a * b, ty),
                    BinOp::Div if b != 0 => TsExpr::Int(a / b, ty),
                    BinOp::Rem if b != 0 => TsExpr::Int(a % b, ty),
                    BinOp::Le => TsExpr::Bool(a <= b),
                    BinOp::Lt => TsExpr::Bool(a < b),
                    BinOp::Ge => TsExpr::Bool(a >= b),
                    BinOp::Gt => TsExpr::Bool(a > b),
                    BinOp::Eq => TsExpr::Bool(a == b),
                    BinOp::Ne => TsExpr::Bool(a != b),
                    _ => TsExpr::Bin { op, lhs: Box::new(l), rhs: Box::new(r), ty },
                };
            }
            TsExpr::Bin { op, lhs: Box::new(l), rhs: Box::new(r), ty }
        }
        TsExpr::If { cond, then_e, else_e, ty } => match fold(*cond) {
            TsExpr::Bool(true) => fold(*then_e),
            TsExpr::Bool(false) => fold(*else_e),
            // A numeric condition: 0 is false, nonzero is true (JS truthiness).
            TsExpr::Int(0, _) => fold(*else_e),
            TsExpr::Int(_, _) => fold(*then_e),
            c => TsExpr::If {
                cond: Box::new(c),
                then_e: Box::new(fold(*then_e)),
                else_e: Box::new(fold(*else_e)),
                ty,
            },
        },
        TsExpr::IndexExpr { base, elem_width, index } => {
            TsExpr::IndexExpr { base, elem_width, index: Box::new(fold(*index)) }
        }
        TsExpr::Call { func, args } => {
            TsExpr::Call { func, args: args.into_iter().map(fold).collect() }
        }
        other => other,
    }
}

/// Substitute parameter variables with their (already-inlined) argument expressions.
/// A record/array base (`obj.field`, `a[i]`) whose name is a parameter bound to a
/// variable argument is RENAMED to that argument — this is how a method's `this`
/// (or an array passed to a helper) re-points to the caller's object.
fn subst(e: &TsExpr, pmap: &HashMap<&str, TsExpr>) -> TsExpr {
    // A base name that is a param mapped to `Var(v)` renames to `v`; else unchanged.
    let rename_base = |base: &str| -> String {
        match pmap.get(base) {
            Some(TsExpr::Var(v)) => v.name.clone(),
            _ => base.to_string(),
        }
    };
    match e {
        TsExpr::Var(v) => pmap.get(v.name.as_str()).cloned().unwrap_or_else(|| e.clone()),
        TsExpr::Bin { op, lhs, rhs, ty } => TsExpr::Bin {
            op: *op,
            lhs: Box::new(subst(lhs, pmap)),
            rhs: Box::new(subst(rhs, pmap)),
            ty: *ty,
        },
        TsExpr::If { cond, then_e, else_e, ty } => TsExpr::If {
            cond: Box::new(subst(cond, pmap)),
            then_e: Box::new(subst(then_e, pmap)),
            else_e: Box::new(subst(else_e, pmap)),
            ty: *ty,
        },
        TsExpr::Field { obj, field, elem_width } => TsExpr::Field {
            obj: rename_base(obj),
            field: field.clone(),
            elem_width: *elem_width,
        },
        TsExpr::Index { base, elem_width, index } => TsExpr::Index {
            base: rename_base(base),
            elem_width: *elem_width,
            index: *index,
        },
        TsExpr::IndexVar { base, elem_width, index_var } => TsExpr::IndexVar {
            base: rename_base(base),
            elem_width: *elem_width,
            index_var: rename_base(index_var),
        },
        TsExpr::IndexExpr { base, elem_width, index } => TsExpr::IndexExpr {
            base: rename_base(base),
            elem_width: *elem_width,
            index: Box::new(subst(index, pmap)),
        },
        TsExpr::Call { func, args } => {
            // A call whose target is a function-valued PARAMETER bound to a named
            // function (`f(x)` where `f` is bound to `inc`) re-targets to that
            // function — this is how a passed-in callback is specialized (the sound
            // first-order case of a higher-order function).
            let new_func = match pmap.get(func.as_str()) {
                Some(TsExpr::Var(v)) => v.name.clone(),
                _ => func.clone(),
            };
            TsExpr::Call { func: new_func, args: args.iter().map(|a| subst(a, pmap)).collect() }
        }
        other => other.clone(),
    }
}
