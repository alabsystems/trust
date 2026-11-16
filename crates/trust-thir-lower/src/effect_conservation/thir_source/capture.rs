//! Capture original Rust source facts, never facts inferred from output IR.
//! Unsupported source constructs refuse the entire capture. In particular this
//! first scope has no borrow/closure escape, projection, control-flow, implicit
//! drop or panic-check implementation. The concrete adapter must prove the
//! complete recorded type footprint needs no drop before using this scope.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{BindingMode, ByRef};
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BinOp, UnOp};
use rustc_middle::thir::{self, BodyTy, Expr, ExprId, ExprKind, LocalVarId, Pat, PatKind, Thir};
use rustc_middle::thir::visit::{self, Visitor};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::LocalDefId;

use super::{CapturedSource, Result, SourceEffect, SourceNode, SourceNodeKind, SourceRoot,
    MAX_SOURCE_DEPTH, MAX_SOURCE_NODES, refuse};

/// Inspect the real local owner; callers cannot supply a made-up THIR/body pair.
/// This is also the read-only analysis entry used by focused actual-TCX probes.
pub fn local(tcx: TyCtxt<'_>, owner: LocalDefId) -> Result<CapturedSource> {
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
        return Err(refuse("owner is not an ordinary source function"));
    }
    let (storage, root) = tcx.thir_body(owner)
        .map_err(|_| refuse("actual owner has no THIR body"))?;
    if storage.is_stolen() { return Err(refuse("actual source THIR was stolen")); }
    let thir = storage.borrow();
    capture(tcx, owner, &thir, root)
}

fn variable(id: LocalVarId, owner: LocalDefId) -> Result<u32> {
    if id.0.owner.def_id != owner { return Err(refuse("variable belongs to another source owner")); }
    Ok(id.0.local_id.as_u32())
}

fn plain_variable(thir: &Thir<'_>, mut id: ExprId) -> Option<LocalVarId> {
    for _ in 0..MAX_SOURCE_DEPTH {
        match thir[id].kind {
            ExprKind::Scope { value, .. } => id = value,
            ExprKind::ValueExpr { source } | ExprKind::PlaceTypeAscription { source, .. }
                | ExprKind::ValueTypeAscription { source, .. } => id = source,
            ExprKind::VarRef { id } => return Some(id),
            _ => return None,
        }
    }
    None
}

fn capture<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, thir: &Thir<'tcx>, root: ExprId)
    -> Result<CapturedSource>
{
    if thir.exprs.len() > MAX_SOURCE_NODES || root.as_usize() >= thir.exprs.len() {
        return Err(refuse("source expression/root budget"));
    }
    let BodyTy::Fn(signature) = thir.body_type else {
        return Err(refuse("THIR body is not a function"));
    };
    if signature.inputs().len() != thir.params.len() {
        return Err(refuse("source signature/parameter population differs"));
    }
    let bindings = crate::template_metadata::rustc::owner_bindings(tcx, owner.to_def_id())
        .map_err(|e| refuse(e.0))?;
    let mut out = Capture { tcx, owner, thir, types: Vec::new(), type_indices: BTreeMap::new(),
        nodes: Vec::new(), effects: Vec::new(), locations: BTreeMap::new(), seen: BTreeSet::new(),
        parameters: BTreeMap::new(), modified: BTreeSet::new(), stack: Vec::new(), key_bytes: 0, depth: 0, refusal: None };
    for (id, expr) in thir.exprs.iter_enumerated() {
        out.locations.insert(expr as *const Expr<'_> as usize, id.as_u32());
        if let ExprKind::Assign { lhs, .. } = expr.kind {
            if let Some(var) = plain_variable(thir, lhs) { out.modified.insert(variable(var, owner)?); }
        }
    }
    let mut argument_types = Vec::new();
    for (index, param) in thir.params.iter().enumerate() {
        argument_types.push(out.ty(param.ty)?);
        let pat = param.pat.as_deref().ok_or_else(|| refuse("implicit parameter needs source transport"))?;
        if let PatKind::Binding { mode: BindingMode(ByRef::No, _), var, subpattern: None, .. } = pat.kind {
            let var = variable(var, owner)?;
            if out.parameters.insert(var, index as u32).is_some() {
                return Err(refuse("two source parameters name one variable"));
            }
        }
        out.visit_pat(pat);
    }
    let return_type = out.ty(signature.output())?;
    out.visit_expr(&thir[root]);
    if let Some(reason) = out.refusal { return Err(reason); }
    if !out.seen.contains(&root.as_u32()) { return Err(refuse("source root was not visited")); }
    let captured = CapturedSource { bindings, target: crate::crate_module::source_target_info(tcx),
        overflow_checks: tcx.sess.overflow_checks(),
        root: root.as_u32(), arena_expressions: thir.exprs.len() as u32,
        argument_variables: (0..argument_types.len()).map(|i|out.parameters.iter()
            .find_map(|(var,index)|(*index as usize==i).then_some(*var))).collect(),
        modified_variables: out.modified.iter().copied().collect(),
        argument_types, return_type, types: out.types, nodes: out.nodes, effects: out.effects };
    super::wire::validate(&captured)?;
    Ok(captured)
}

struct Capture<'a, 'tcx> {
    tcx: TyCtxt<'tcx>, owner: LocalDefId, thir: &'a Thir<'tcx>,
    types: Vec<trust_ir::template::HostKey>,
    type_indices: BTreeMap<(String, Vec<u8>), u32>,
    nodes: Vec<SourceNode>, effects: Vec<SourceEffect>, locations: BTreeMap<usize, u32>,
    seen: BTreeSet<u32>, parameters: BTreeMap<u32, u32>, modified: BTreeSet<u32>,
    stack: Vec<usize>,
    key_bytes: usize, depth: usize, refusal: Option<super::SourceRefusal>,
}
impl<'tcx> Capture<'_, 'tcx> {
    fn key_budget(&mut self, key: &trust_ir::template::HostKey) -> Result<()> {
        self.key_bytes=self.key_bytes.saturating_add(key.namespace.len()).saturating_add(key.bytes.len());
        if self.key_bytes>super::wire::MAX_BYTES { return Err(refuse("captured source key byte budget")); }
        Ok(())
    }
    fn ty(&mut self, source: ty::Ty<'tcx>) -> Result<u32> {
        let key = crate::template_key::rustc::checked_type_key(self.tcx, source, self.owner.to_def_id())
            .map_err(|e| refuse(e.to_string()))?;
        let key = crate::template_key::encode(&crate::template_key::HoleKey::Type(key))
            .map_err(|e| refuse(e.to_string()))?;
        let identity = (key.namespace.clone(), key.bytes.clone());
        if let Some(id) = self.type_indices.get(&identity) { return Ok(*id); }
        if self.types.len() >= MAX_SOURCE_NODES { return Err(refuse("source type budget")); }
        self.key_budget(&key)?;
        let index = self.types.len() as u32; self.type_indices.insert(identity, index);
        self.types.push(key); Ok(index)
    }
    fn classify(&mut self, expr: &Expr<'tcx>, location: u32, ty: u32) -> Result<SourceNodeKind> {
        use ExprKind::*;
        Ok(match &expr.kind {
            Scope { .. } | ValueExpr { .. } | PlaceTypeAscription { .. }
                | ValueTypeAscription { .. } => SourceNodeKind::Wrapper,
            NeverToAny { .. } => SourceNodeKind::NeverCoercion,
            Block { .. } => SourceNodeKind::Block,
            Literal { lit, .. } if matches!(lit.node,
                rustc_ast::LitKind::Bool(_) | rustc_ast::LitKind::Int(..) | rustc_ast::LitKind::Char(_)) => SourceNodeKind::Literal,
            ZstLiteral { .. } => SourceNodeKind::Literal,
            VarRef { id } => SourceNodeKind::Variable(variable(*id, self.owner)?),
            Return { .. } => SourceNodeKind::Return,
            Array { .. } => SourceNodeKind::Array,
            Tuple { .. } => SourceNodeKind::Tuple,
            Repeat { .. } => SourceNodeKind::Repeat,
            Cast { .. } => SourceNodeKind::Cast,
            Unary { op: UnOp::Not, .. } => SourceNodeKind::Not,
            Binary { op: BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, .. } => SourceNodeKind::Bitwise,
            Binary { op: BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, .. } => SourceNodeKind::Compare,
            // A read may dereference a caller pointer. No NoUB premise is created.
            Deref { .. } => SourceNodeKind::Dereference,
            Call { fun, args, .. } => {
                let ty::FnDef(def, generic_args) = *self.thir[*fun].ty.kind() else {
                    return Err(refuse("indirect/closure call needs complete source transport"));
                };
                if self.tcx.intrinsic(def).is_some() {
                    return Err(refuse("intrinsic call needs its source effect semantics"));
                }
                let key = crate::template_key::rustc::checked_call_key(self.tcx, def,
                    generic_args.skip_binder(), self.owner.to_def_id())
                    .map_err(|e| refuse(e.to_string()))?;
                let key = crate::template_key::encode(&key).map_err(|e| refuse(e.to_string()))?;
                let argument_types = args.iter().map(|id| self.ty(self.thir[*id].ty)).collect::<Result<_>>()?;
                self.key_budget(&key)?;
                self.effects.push(SourceEffect::Call { expression: location, key, argument_types, result_type: ty });
                SourceNodeKind::Call
            }
            Assign { lhs, rhs } => {
                if let Some(var) = plain_variable(self.thir, *lhs) {
                    SourceNodeKind::LocalAssignment(variable(var, self.owner)?)
                } else {
                    let mut place = *lhs;
                    while let Scope { value, .. } = self.thir[place].kind { place = value; }
                    let Deref { arg } = self.thir[place].kind else {
                        return Err(refuse("store projection needs complete source transport"));
                    };
                    let root = plain_variable(self.thir, arg).and_then(|var| variable(var, self.owner).ok())
                        .filter(|var| !self.modified.contains(var)).and_then(|var| self.parameters.get(&var).copied())
                        .map(SourceRoot::Argument).unwrap_or(SourceRoot::Indirect);
                    let exact_argument = plain_variable(self.thir, *rhs).and_then(|var| variable(var, self.owner).ok())
                        .filter(|var| !self.modified.contains(var)).and_then(|var| self.parameters.get(&var).copied());
                    let value_type = self.ty(self.thir[*rhs].ty)?;
                    self.effects.push(SourceEffect::Store { expression: location, root, value_type, exact_argument });
                    SourceNodeKind::EscapingStore
                }
            }
            _ => return Err(refuse(format!("unsupported source expression at arena index {location}"))),
        })
    }
}

impl<'a, 'tcx: 'a> Visitor<'a, 'tcx> for Capture<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> { self.thir }
    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        if self.refusal.is_some() { return; }
        let result = (|| {
            let location = *self.locations.get(&(expr as *const Expr<'_> as usize))
                .ok_or_else(|| refuse("visited expression is outside the actual THIR arena"))?;
            if self.depth >= MAX_SOURCE_DEPTH || !self.seen.insert(location) {
                return Err(refuse("recursive/shared source expression or depth budget"));
            }
            let ty = self.ty(expr.ty)?;
            let kind = self.classify(expr, location, ty)?;
            let index = self.nodes.len();
            if let Some(&parent) = self.stack.last() { self.nodes[parent].children.push(location); }
            self.nodes.push(SourceNode { expression: location, ty, kind, children: Vec::new() });
            self.stack.push(index);
            self.depth += 1; visit::walk_expr(self, expr); self.depth -= 1;
            self.stack.pop();
            Ok(())
        })();
        if let Err(error) = result { self.refusal = Some(error); }
    }
    fn visit_pat(&mut self, pat: &'a Pat<'tcx>) {
        if self.refusal.is_some() { return; }
        let result = (|| {
            self.ty(pat.ty)?;
            match &pat.kind {
                PatKind::Wild => {},
                PatKind::Binding { mode: BindingMode(ByRef::No, _), var, ty, subpattern: None, .. } => {
                    variable(*var, self.owner)?; self.ty(*ty)?;
                }
                _ => return Err(refuse("pattern borrow/projection/control needs complete source transport")),
            }
            Ok(())
        })();
        if let Err(error) = result { self.refusal = Some(error); }
    }
}
