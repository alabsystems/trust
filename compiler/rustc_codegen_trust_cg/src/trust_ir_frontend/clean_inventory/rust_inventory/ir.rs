//! Trust: explicit IR inventory fragment, with no rustc namespace dependency.
//! Source identity and THIR completeness are checked by the production caller.

use std::collections::BTreeSet;

use trust_ir::function_dependencies::{
    DependencyNode, DependencySite, inspect_defined_function_dependencies,
};
use trust_ir::{BinOp, CastOp, Constant, FuncId, Function, Inst, Module, Producer, Ty, UnOp};

/// One canonical reading of an immutable original module. This supplies no
/// source, body or proof authority; the caller binds the exact retained Arc.
#[derive(Default)]
pub(super) struct ModuleInventory {
    call_free: BTreeSet<FuncId>,
}

impl ModuleInventory {
    pub(super) fn new(module: &Module) -> Self {
        if !trust_ir_build::validate_module(module).is_empty() {
            return Self::default();
        }
        let census = inspect_defined_function_dependencies(module);
        let mut blocked = BTreeSet::new();
        for refusal in census.refusals() {
            match refusal.site {
                DependencySite::Definition(DependencyNode::Function(id))
                | DependencySite::Instruction { function: id, .. } => {
                    blocked.insert(id);
                }
                _ => return Self::default(),
            }
        }
        for edge in census.edges() {
            if let DependencySite::Instruction { function, .. } = edge.site
                && matches!(edge.target, DependencyNode::Function(_) | DependencyNode::Global(_))
            {
                blocked.insert(function);
            }
        }
        Self {
            call_free: module
                .functions
                .iter()
                .filter(|f| !blocked.contains(&f.id) && primitive_body(module, f))
                .map(|f| f.id)
                .collect(),
        }
    }

    pub(super) fn call_free(&self, function: FuncId) -> bool {
        self.call_free.contains(&function)
    }
}

fn scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
    )
}

fn scalar_or_pointer(ty: &Ty) -> bool {
    scalar(ty) || *ty == Ty::Ptr
}

/// The source guard admits primitive expressions and scalar local cells.
/// The dependency census independently checks the exact original row; zero
/// explicit edges alone could not establish the absence of implicit services.
fn primitive_body(module: &Module, function: &Function) -> bool {
    let Some(signature) = module.func_types.get(function.ty.as_usize()) else { return false };
    if function.blocks.is_empty()
        || function.producer != Some(Producer::TRust)
        || signature.is_vararg
        || !signature.params.iter().chain(&signature.returns).all(scalar_or_pointer)
    {
        return false;
    }
    for block in &function.blocks {
        if !block.params.iter().all(|(_, ty)| scalar_or_pointer(ty)) {
            return false;
        }
        for node in &block.body {
            let admitted = match &node.inst {
                Inst::Const { ty, value: Constant::Int(_) | Constant::Bool(_) } => scalar(ty),
                Inst::BinOp {
                    op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor,
                    ty,
                    ..
                }
                | Inst::UnOp { op: UnOp::Not, ty, .. } => scalar(ty),
                Inst::ICmp { ty, .. } => scalar_or_pointer(ty),
                Inst::Alloca { ty, count: None, .. }
                | Inst::Load { ty, volatile: false, .. }
                | Inst::Store { ty, volatile: false, .. } => scalar(ty),
                Inst::Cast {
                    op: CastOp::ZExt | CastOp::SExt | CastOp::Trunc,
                    src_ty,
                    dst_ty,
                    ..
                } => scalar(src_ty) && scalar(dst_ty),
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Return { .. } => true,
                _ => false,
            };
            if !admitted {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
// Trust: out-of-line unit tests, as tidy's `unit_tests` check requires.
#[path = "ir/tests.rs"]
mod tests;
