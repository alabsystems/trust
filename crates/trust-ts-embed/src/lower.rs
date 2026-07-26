//! The `TsCore → trust_types::VerifiableFunction` deriver — the load-bearing
//! lowering. It turns the expression-oriented core into an SSA-ish CFG:
//! parameters become locals `1..=arg_count`, the return slot is local `0`, each
//! sub-expression gets a fresh temporary, and every `If` expression becomes a
//! `SwitchInt` + `Goto` diamond (there is no `Select` rvalue). The resulting image
//! is what the refinement toolchain compares against a Rust port's image.
//!
//! Names are preserved on parameters/bindings so the name/Ty-aware
//! `SimulationRelation` can align this TS-image with a differently-laid-out Rust
//! image. Anything the deriver cannot model fails closed as a [`FragmentEscape`].

use std::collections::HashMap;

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use crate::core::{TsExpr, TsFunction, TsStmt, TsTy};
use crate::escape::{FragmentEscape, UnsupportedTsConstruct};

struct Lowerer {
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    cur_id: usize,
    cur_stmts: Vec<Statement>,
    next_block: usize,
    names: HashMap<String, usize>,
    returned: bool,
    symbol: String,
}

impl Lowerer {
    fn new_local(&mut self, ty: Ty, name: Option<String>) -> usize {
        let idx = self.locals.len();
        self.locals.push(LocalDecl { index: idx, ty, name });
        idx
    }

    fn fresh_block(&mut self) -> usize {
        let id = self.next_block;
        self.next_block += 1;
        id
    }

    /// Finish the block currently being built with terminator `term`.
    fn emit(&mut self, term: Terminator) {
        let stmts = std::mem::take(&mut self.cur_stmts);
        self.blocks.push(BasicBlock { id: BlockId(self.cur_id), stmts, terminator: term });
    }

    /// Begin building block `id`.
    fn start(&mut self, id: usize) {
        self.cur_id = id;
        self.cur_stmts.clear();
    }

    fn assign(&mut self, place_local: usize, rvalue: Rvalue) {
        self.cur_stmts.push(Statement::Assign {
            place: Place::local(place_local),
            rvalue,
            span: SourceSpan::default(),
        });
    }

    fn copy(i: usize) -> Operand {
        Operand::Copy(Place::local(i))
    }

    /// Lower an expression, returning the local holding its value. May emit blocks
    /// (and move the "current block" to a fresh merge block) when it contains `If`.
    fn lower_expr(&mut self, e: &TsExpr) -> Result<usize, FragmentEscape> {
        match e {
            TsExpr::Int(v, ty) => {
                let t = self.new_local(ty.to_ty(), None);
                let cv = match ty {
                    TsTy::Num { width, signed: false } => ConstValue::Uint(*v as u128, *width),
                    TsTy::Num { signed: true, .. } => ConstValue::Int(*v),
                    TsTy::Bool => ConstValue::Uint(u128::from(*v != 0), 1),
                    // An integer literal is never array-typed; arrays never reach
                    // this deriver (rejected up front). Fail closed, never panic.
                    TsTy::Arr { .. } => {
                        return Err(FragmentEscape::new(
                            &self.symbol,
                            UnsupportedTsConstruct::UnknownConstruct {
                                detail: "array-typed integer literal".to_string(),
                            },
                        ));
                    }
                };
                self.assign(t, Rvalue::Use(Operand::Constant(cv)));
                Ok(t)
            }
            TsExpr::Bool(b) => {
                let t = self.new_local(Ty::Bool, None);
                self.assign(t, Rvalue::Use(Operand::Constant(ConstValue::Uint(u128::from(*b), 1))));
                Ok(t)
            }
            TsExpr::Var(v) => self
                .names
                .get(&v.name)
                .copied()
                .ok_or_else(|| FragmentEscape::unbound_var(&self.symbol, &v.name)),
            TsExpr::Bin { op, lhs, rhs, ty } => {
                let l = self.lower_expr(lhs)?;
                let r = self.lower_expr(rhs)?;
                let t = self.new_local(ty.to_ty(), None);
                self.assign(t, Rvalue::BinaryOp(*op, Self::copy(l), Self::copy(r)));
                Ok(t)
            }
            TsExpr::If { cond, then_e, else_e, ty } => {
                let c = self.lower_expr(cond)?;
                let result = self.new_local(ty.to_ty(), None);
                let then_id = self.fresh_block();
                let else_id = self.fresh_block();
                let merge_id = self.fresh_block();
                self.emit(Terminator::SwitchInt {
                    discr: Self::copy(c),
                    targets: vec![(1, BlockId(then_id))],
                    otherwise: BlockId(else_id),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                });
                // then arm
                self.start(then_id);
                let ti = self.lower_expr(then_e)?;
                self.assign(result, Rvalue::Use(Self::copy(ti)));
                self.emit(Terminator::Goto(BlockId(merge_id)));
                // else arm
                self.start(else_id);
                let ei = self.lower_expr(else_e)?;
                self.assign(result, Rvalue::Use(Self::copy(ei)));
                self.emit(Terminator::Goto(BlockId(merge_id)));
                // continue in the merge block
                self.start(merge_id);
                Ok(result)
            }
            TsExpr::Index { .. }
            | TsExpr::IndexVar { .. }
            | TsExpr::Field { .. }
            | TsExpr::IndexExpr { .. } => {
                Err(FragmentEscape::new(
                    &self.symbol,
                    UnsupportedTsConstruct::UnknownConstruct {
                        detail: "array/record access is admitted via the denotational path \
                                 (Sort::Array + Select / field vars), not the VerifiableFunction \
                                 deriver"
                            .to_string(),
                    },
                ))
            }
            TsExpr::Call { func, .. } => Err(FragmentEscape::new(
                &self.symbol,
                UnsupportedTsConstruct::UnmodeledCall { callee: func.clone() },
            )),
        }
    }

    fn lower_stmt(&mut self, s: &TsStmt) -> Result<(), FragmentEscape> {
        match s {
            TsStmt::Assign { var, value } => {
                let vi = self.lower_expr(value)?;
                let li = if let Some(&i) = self.names.get(&var.name) {
                    i
                } else {
                    let i = self.new_local(var.ty.to_ty(), Some(var.name.clone()));
                    self.names.insert(var.name.clone(), i);
                    i
                };
                self.assign(li, Rvalue::Use(Self::copy(vi)));
                Ok(())
            }
            TsStmt::Return { value } => {
                let vi = self.lower_expr(value)?;
                self.assign(0, Rvalue::Use(Self::copy(vi)));
                self.emit(Terminator::Return);
                self.returned = true;
                Ok(())
            }
            TsStmt::ForRange { .. } => Err(FragmentEscape::new(
                &self.symbol,
                UnsupportedTsConstruct::UnsupportedControlFlow {
                    kind: "bounded for-loop (admitted via the denotational unroll path, not the \
                           VerifiableFunction deriver)"
                        .to_string(),
                },
            )),
        }
    }
}

/// Lower a [`TsFunction`] to a [`VerifiableFunction`], or fail closed with a
/// [`FragmentEscape`].
pub fn lower_function(f: &TsFunction) -> Result<VerifiableFunction, FragmentEscape> {
    let mut lo = Lowerer {
        locals: Vec::new(),
        blocks: Vec::new(),
        cur_id: 0,
        cur_stmts: Vec::new(),
        next_block: 1,
        names: HashMap::new(),
        returned: false,
        symbol: f.name.clone(),
    };

    // Arrays lower only via the denotational path; the VerifiableFunction deriver
    // fails closed on an array-typed parameter (never a silent partial body).
    if let Some(p) = f.params.iter().find(|p| matches!(p.ty, TsTy::Arr { .. })) {
        return Err(FragmentEscape::new(
            &f.name,
            UnsupportedTsConstruct::UnknownConstruct {
                detail: format!("array-typed parameter `{}` lowers via the denotational path", p.name),
            },
        ));
    }

    // local 0 = return slot
    lo.new_local(f.ret.to_ty(), None);
    // params = locals 1..=arg_count (named, so the relation can align by name)
    for p in &f.params {
        let i = lo.new_local(p.ty.to_ty(), Some(p.name.clone()));
        lo.names.insert(p.name.clone(), i);
    }

    for s in &f.body {
        lo.lower_stmt(s)?;
    }
    if !lo.returned {
        return Err(FragmentEscape::no_return(&f.name));
    }

    Ok(VerifiableFunction {
        name: f.name.clone(),
        def_path: f.def_path.clone(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: lo.locals,
            blocks: lo.blocks,
            arg_count: f.params.len(),
            return_ty: f.ret.to_ty(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{TsExpr, TsVar};

    /// The deriver fails CLOSED on every construct outside its scalar fragment
    /// (arrays, records, bounded loops, missing return) — never a silent partial
    /// `VerifiableFunction`. These are admitted via the denotational path instead.
    #[test]
    fn lower_fails_closed_on_out_of_fragment() {
        let u = TsTy::uint(16);
        let ret = |value| TsFunction {
            name: "f".into(),
            def_path: "f".into(),
            params: vec![],
            body: vec![TsStmt::Return { value }],
            ret: u,
        };

        // Array parameter + index.
        let arr = TsFunction {
            params: vec![TsVar::new("a", TsTy::array(16, 2))],
            ..ret(TsExpr::index("a", 16, 0))
        };
        assert!(lower_function(&arr).is_err(), "array function must fail closed");

        // Record field access.
        assert!(lower_function(&ret(TsExpr::field("s", "x", 16))).is_err(), "record must fail closed");

        // Bounded loop.
        let loopy = TsFunction {
            body: vec![TsStmt::ForRange { var: "i".into(), count: 2, body: vec![] }],
            ..ret(TsExpr::Int(0, u))
        };
        assert!(lower_function(&loopy).is_err(), "loop must fail closed");

        // No return.
        let noret =
            TsFunction { body: vec![], ..ret(TsExpr::Int(0, u)) };
        assert!(lower_function(&noret).is_err(), "missing return must fail closed");

        // Scalar functions still lower fine (the fragment is non-empty).
        assert!(lower_function(&ret(TsExpr::Int(7, u))).is_ok());
    }
}
