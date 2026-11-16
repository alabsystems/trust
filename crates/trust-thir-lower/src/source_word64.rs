// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Original typed Rust source data for a bounded word64 semantic vocabulary.
//!
//! Capture reads the actual owner's THIR, before inspecting any emitted IR.
//! A registered builtin and an ordinary Rust call remain distinct. In particular,
//! a core-wrapper name or version fingerprint never converts a Rust call into an
//! addition primitive. Ordinary callees still need their own source/IR evidence.
//!
//! This borrowed snapshot is not a proof, source-refinement certificate, purity,
//! termination, ABI, NoUB or codegen capability. No decoder can construct it.
//! Serialization and production metadata integration remain separate work.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use rustc_hir::def::DefKind;
use rustc_hir::{BindingMode, ByRef};
use rustc_middle::thir::{BlockSafety, ExprId, ExprKind, LocalVarId, PatKind, Thir};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::SourceFile;
use rustc_span::def_id::{DefId, LocalDefId};

#[path = "source_word64/record.rs"]
pub mod record;

const MAX_EXPRESSIONS: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceRefusal(pub String);
impl std::fmt::Display for SourceRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "word64 Rust source: {}", self.0)
    }
}
impl std::error::Error for SourceRefusal {}
fn refuse(message: &str) -> SourceRefusal {
    SourceRefusal(message.into())
}
type Result<T> = std::result::Result<T, SourceRefusal>;

// The portable record vocabulary is shared with independent kernel readers.
pub use record::{CallKind, Operand};

#[derive(Debug)]
pub struct SourceCall<'tcx> {
    definition: DefId,
    arguments: ty::GenericArgs<'tcx>,
    kind: CallKind,
    expression: usize,
    operands: Vec<(usize, Operand)>,
}
impl<'tcx> SourceCall<'tcx> {
    pub fn definition(&self) -> DefId {
        self.definition
    }
    pub fn arguments(&self) -> ty::GenericArgs<'tcx> {
        self.arguments
    }
    pub fn kind(&self) -> CallKind {
        self.kind
    }
    pub fn expression(&self) -> usize {
        self.expression
    }
    pub fn operands(&self) -> &[(usize, Operand)] {
        &self.operands
    }
}

#[derive(Debug)]
pub enum Expression<'tcx> {
    Operand { expression: usize, value: Operand },
    Call(SourceCall<'tcx>),
}

/// An actual same-session source observation. Fields are private and there is
/// no wire/data constructor. It retains original parameter identities and the
/// original immutable source-file allocation, not a replacement source string.
/// It grants no permission to use an emitted body or an arbitrary callee model.
pub struct CapturedSource<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    source_file: Arc<SourceFile>,
    parameters: Vec<LocalVarId>,
    expression: Expression<'tcx>,
    visited: Vec<usize>,
}
impl<'tcx> CapturedSource<'tcx> {
    /// Erase the borrow into an explicitly untrusted source claim for metadata.
    /// This never reconstructs a live snapshot and grants no proof/admission.
    pub fn to_record(&self) -> Result<record::Record> {
        let definition = |def: DefId| {
            let hash = self.tcx.def_path_hash(def);
            record::Definition {
                stable_crate_id: hash.stable_crate_id().as_u64(),
                local_hash: hash.local_hash().as_u64(),
            }
        };
        let body = match &self.expression {
            Expression::Operand { expression, value } => {
                record::Body::Operand { node: *expression as u32, value: value.clone() }
            }
            Expression::Call(call) => {
                let arguments = call.arguments();
                let generic_u64 = match arguments.len() {
                    0 => false,
                    1 if arguments[0].as_type() == Some(self.tcx.types.u64) => true,
                    _ => {
                        return Err(refuse(
                            "source substitutions need their own stable vocabulary",
                        ));
                    }
                };
                record::Body::Call {
                    node: call.expression as u32,
                    definition: definition(call.definition),
                    kind: call.kind,
                    generic_u64,
                    operands: call
                        .operands
                        .iter()
                        .map(|(id, value)| (*id as u32, value.clone()))
                        .collect(),
                }
            }
        };
        let record = record::Record {
            owner: definition(self.owner.to_def_id()),
            parameters: self.parameters.iter().map(|var| var.0.local_id.as_u32()).collect(),
            expressions: self.visited.len() as u32,
            source_hash: self.source_file.src_hash.to_string(),
            body,
        };
        record.validate().map_err(|error| SourceRefusal(error.to_string()))?;
        Ok(record)
    }

    pub fn owner(&self) -> LocalDefId {
        self.owner
    }
    pub fn parameters(&self) -> &[LocalVarId] {
        &self.parameters
    }
    pub fn expression(&self) -> &Expression<'tcx> {
        &self.expression
    }
    pub fn original_expressions(&self) -> &[usize] {
        &self.visited
    }
    pub fn source_file(&self) -> &Arc<SourceFile> {
        &self.source_file
    }
    /// Same session and original owner only; not a returned-value/IR judgment.
    pub fn belongs_to(&self, tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
        std::ptr::eq(self.tcx.sess, tcx.sess) && self.owner == owner
    }
}

/// Capture an actual ordinary local source definition. No caller supplies THIR,
/// parameter maps, intrinsic labels, emitted IR, proof terms or an accepted bit.
/// The initial vocabulary is one/two U64 inputs, one complete safe block, and a
/// variable/literal or one direct call with variable/literal operands. Unsupported
/// constructs refuse the whole capture; no partial snapshot is returned.
pub fn capture<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Result<CapturedSource<'tcx>> {
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
        return Err(refuse("owner is not an ordinary source function"));
    }
    if tcx.intrinsic(owner).is_some() {
        return Err(refuse("intrinsic declaration is not an ordinary source body"));
    }
    if tcx.generics_of(owner).requires_monomorphization(tcx) {
        return Err(refuse("generic source owner requires a separate instance source"));
    }
    let signature = tcx.fn_sig(owner).instantiate_identity().skip_normalization().skip_binder();
    if !matches!(signature.inputs().len(), 1 | 2)
        || signature.inputs().iter().any(|ty| *ty != tcx.types.u64)
        || signature.output() != tcx.types.u64
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
    {
        return Err(refuse("requires a safe nonvariadic Rust U64 signature"));
    }
    let source_span = tcx.def_span(owner);
    if source_span.is_dummy() {
        return Err(refuse("original source location absent"));
    }
    let (storage, root) = tcx.thir_body(owner).map_err(|_| refuse("actual source THIR absent"))?;
    if storage.is_stolen() {
        return Err(refuse("actual source THIR already stolen"));
    }
    let thir = storage.borrow();
    if thir.exprs.len() > MAX_EXPRESSIONS
        || thir.blocks.len() != 1
        || !thir.stmts.is_empty()
        || thir.params.len() != signature.inputs().len()
    {
        return Err(refuse("complete original expression/block/statement population"));
    }
    let mut parameters = Vec::new();
    let mut variables = HashMap::new();
    for (index, parameter) in thir.params.iter().enumerate() {
        let pat = parameter.pat.as_ref().ok_or_else(|| refuse("explicit original parameter"))?;
        let PatKind::Binding { mode: BindingMode(ByRef::No, _), var, subpattern: None, .. } =
            pat.kind
        else {
            return Err(refuse("original by-value parameter binding"));
        };
        if var.0.owner.def_id != owner
            || parameter.ty != tcx.types.u64
            || pat.ty != tcx.types.u64
            || variables.insert(var, index as u32).is_some()
        {
            return Err(refuse("parameter owner, identity, population or U64 type"));
        }
        parameters.push(var);
    }
    let mut reader = Reader { tcx, thir: &thir, variables, visited: BTreeSet::new() };
    let outer = reader.peel(root)?;
    let ExprKind::Block { block } = thir.exprs[outer].kind else {
        return Err(refuse("original function block"));
    };
    let body = &thir.blocks[block];
    if body.targeted_by_break
        || !body.stmts.is_empty()
        || !matches!(body.safety_mode, BlockSafety::Safe)
    {
        return Err(refuse("one complete safe source block"));
    }
    let expression = reader.peel(body.expr.ok_or_else(|| refuse("original source tail"))?)?;
    let expression = match thir.exprs[expression].kind {
        ExprKind::Call { fun, ref args, from_hir_call: true, .. } => {
            if args.len() != 2 || thir.exprs[expression].ty != tcx.types.u64 {
                return Err(refuse("bounded U64 source call result/arity"));
            }
            let fun = reader.peel(fun)?;
            if !matches!(thir.exprs[fun].kind, ExprKind::ZstLiteral { .. }) {
                return Err(refuse("effect-free original function item"));
            }
            let ty::FnDef(definition, substitutions) = *thir.exprs[fun].ty.kind() else {
                return Err(refuse("original typed FnDef"));
            };
            let arguments = substitutions.skip_binder();
            let signature = tcx
                .fn_sig(definition)
                .instantiate(tcx, arguments)
                .skip_normalization()
                .skip_binder();
            if signature.inputs() != [tcx.types.u64, tcx.types.u64]
                || signature.output() != tcx.types.u64
                || signature.c_variadic()
                || signature.safety() != rustc_hir::Safety::Safe
                || signature.abi() != rustc_abi::ExternAbi::Rust
            {
                return Err(refuse("actual instantiated source call signature"));
            }
            let kind = match tcx.intrinsic(definition) {
                None => CallKind::OrdinaryCall,
                Some(intrinsic) => {
                    let core = tcx
                        .lang_items()
                        .sized_trait()
                        .ok_or_else(|| refuse("actual core language-item owner absent"))?
                        .krate;
                    if definition.krate != core
                        || !intrinsic.must_be_overridden
                        || intrinsic.name.as_str() != "wrapping_add"
                    {
                        return Err(refuse("unsupported registered source intrinsic"));
                    }
                    CallKind::RegisteredWrappingAdd
                }
            };
            let mut operands = Vec::new();
            for arg in args {
                let id = reader.peel(*arg)?;
                operands.push((id.as_usize(), reader.operand(id)?));
            }
            Expression::Call(SourceCall {
                definition,
                arguments,
                kind,
                expression: expression.as_usize(),
                operands,
            })
        }
        _ => Expression::Operand {
            expression: expression.as_usize(),
            value: reader.operand(expression)?,
        },
    };
    if reader.visited.len() != thir.exprs.len() {
        return Err(refuse("unaccounted original source expression"));
    }
    let visited = reader.visited.into_iter().collect();
    let source_file = tcx.sess.source_map().lookup_source_file(source_span.lo());
    Ok(CapturedSource { tcx, owner, source_file, parameters, expression, visited })
}

struct Reader<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    variables: HashMap<LocalVarId, u32>,
    visited: BTreeSet<usize>,
}
impl Reader<'_, '_> {
    fn peel(&mut self, mut id: ExprId) -> Result<ExprId> {
        loop {
            if id.as_usize() >= self.thir.exprs.len() || !self.visited.insert(id.as_usize()) {
                return Err(refuse("invalid or repeated original expression"));
            }
            match self.thir.exprs[id].kind {
                ExprKind::Scope { value, .. } => id = value,
                ExprKind::ValueExpr { source }
                | ExprKind::PlaceTypeAscription { source, .. }
                | ExprKind::ValueTypeAscription { source, .. } => id = source,
                _ => return Ok(id),
            }
        }
    }
    fn operand(&self, id: ExprId) -> Result<Operand> {
        if self.thir.exprs[id].ty != self.tcx.types.u64 {
            return Err(refuse("source operand U64 type"));
        }
        match self.thir.exprs[id].kind {
            ExprKind::VarRef { id } => self
                .variables
                .get(&id)
                .copied()
                .map(Operand::Parameter)
                .ok_or_else(|| refuse("operand is not an original parameter")),
            ExprKind::Literal { lit, neg: false } => match lit.node {
                rustc_ast::LitKind::Int(value, _) => u64::try_from(value.get())
                    .map(Operand::Literal)
                    .map_err(|_| refuse("source literal exceeds U64")),
                _ => Err(refuse("noninteger source literal")),
            },
            _ => Err(refuse("source operand requires its own supported semantics")),
        }
    }
}
