//! Trust: explicit IR inventory fragment, with no rustc namespace dependency.
//! Source identity and THIR completeness are checked by the production caller.

use std::collections::BTreeSet;

use trust_ir::function_dependencies::{
    DependencyNode, DependencySite, inspect_defined_function_dependencies,
};
use trust_ir::{BinOp, Constant, FuncId, Function, Inst, Module, Producer, Ty, UnOp};

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
    )
}

/// The source guard currently admits call-free primitive expressions only.
/// The dependency census independently checks the exact original row; zero
/// explicit edges alone could not establish the absence of implicit services.
fn primitive_body(module: &Module, function: &Function) -> bool {
    let Some(signature) = module.func_types.get(function.ty.as_usize()) else { return false };
    if function.blocks.is_empty()
        || function.producer != Some(Producer::TRust)
        || !signature.params.iter().chain(&signature.returns).all(scalar)
    {
        return false;
    }
    for block in &function.blocks {
        if !block.params.iter().all(|(_, ty)| scalar(ty)) {
            return false;
        }
        for node in &block.body {
            let admitted = match &node.inst {
                Inst::Const { ty, value: Constant::Int(_) | Constant::Bool(_) } => scalar(ty),
                Inst::BinOp { op: BinOp::And | BinOp::Or | BinOp::Xor, ty, .. }
                | Inst::UnOp { op: UnOp::Not, ty, .. }
                | Inst::ICmp { ty, .. } => scalar(ty),
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
mod tests;
