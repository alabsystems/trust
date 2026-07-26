//! Trust: Compiler-owned proof item IR.
//!
//! `proof fn` must lower to a compiler-owned item, not to an attribute or proc
//! macro expansion. Parser/HIR support can land incrementally, but MIR-facing
//! verification should consume proof items through this typed model alongside
//! `TrustContractBundle`.

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_macros::{StableHash, TyDecodable, TyEncodable};
use rustc_span::{Span, Symbol};

use crate::ty::Ty;

rustc_index::newtype_index! {
    /// Dense per-owner index for compiler-owned Trust proof items.
    #[stable_hash]
    #[encodable]
    #[orderable]
    #[debug_format = "TrustProofItemId({})"]
    pub struct TrustProofItemId {}
}

/// Proof items attached to a module, crate, or function owner.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofItemBundle<'tcx> {
    /// Owner whose proof namespace this bundle describes.
    pub owner: DefId,
    /// Compiler-owned proof items indexed by dense proof item id.
    pub items: IndexVec<TrustProofItemId, TrustProofItem<'tcx>>,
    /// Deterministic summary for diagnostics and downstream admission checks.
    pub summary: TrustProofItemSummary,
}

impl<'tcx> TrustProofItemBundle<'tcx> {
    /// Build an empty proof item bundle for an owner.
    #[must_use]
    pub fn empty(owner: DefId) -> Self {
        Self { owner, items: IndexVec::new(), summary: TrustProofItemSummary::default() }
    }

    /// Returns true when no compiler-owned proof items are available.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Lookup a proof item by dense id.
    #[must_use]
    pub fn proof_item(&self, id: TrustProofItemId) -> Option<&TrustProofItem<'tcx>> {
        self.items.get(id)
    }
}

/// One compiler-owned proof item after parsing/lowering.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofItem<'tcx> {
    /// Stable source-level name for diagnostics and cross-crate metadata.
    pub name: Symbol,
    /// DefId of the proof item itself.
    pub def_id: DefId,
    /// What kind of proof item this is.
    pub kind: TrustProofItemKind,
    /// Where this proof item is allowed to apply.
    pub target: TrustProofTarget,
    /// Typed signature visible to proof checking.
    pub signature: TrustProofSignature<'tcx>,
    /// Verification-only body representation.
    pub body: TrustProofBody,
    /// Source that introduced the proof item.
    pub source: TrustProofItemSource,
    /// Whole item span for diagnostics.
    pub span: Span,
}

impl TrustProofItem<'_> {
    /// Proof items are verification artifacts and must not produce runtime code.
    #[must_use]
    pub fn is_runtime_erased(&self) -> bool {
        matches!(self.kind, TrustProofItemKind::ProofFn | TrustProofItemKind::Lemma)
    }
}

/// Proof item roles understood by the compiler boundary.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofItemKind {
    /// Native `proof fn`: a lemma-like function verified and erased.
    ProofFn,
    /// Solver lemma synthesized or imported by Trust.
    Lemma,
}

/// Where a proof item is meant to discharge obligations.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofTarget {
    /// Proof item is available in the enclosing proof namespace.
    LocalNamespace,
    /// Proof item supports a specific Rust item.
    Item { def_id: DefId },
    /// Proof item supports one compiler-owned contract in a function bundle.
    Contract { def_id: DefId, contract_index: u32 },
}

/// Typed proof item signature.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofSignature<'tcx> {
    pub inputs: Vec<TrustProofParam<'tcx>>,
    pub output: Option<Ty<'tcx>>,
}

/// One proof item parameter.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofParam<'tcx> {
    pub name: Option<Symbol>,
    pub ty: Ty<'tcx>,
    pub span: Span,
}

/// Verification-only body representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofBody {
    /// Body is held by the compiler HIR/MIR owner and must be erased before codegen.
    CompilerOwned { body_def_id: DefId },
    /// Body is an opaque proof script owned by a native proof engine.
    NativeScript { engine: Symbol, text: Symbol },
    /// The frontend found a proof item but could not lower its body.
    Unsupported { reason: Symbol },
}

/// Origin of a proof item.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustProofItemSource {
    /// User-written native Trust syntax, such as `proof fn`.
    NativeSyntax,
    /// Compiler-synthesized lemma or proof helper.
    Synthesized,
    /// Cross-crate metadata decoded from an upstream rlib.
    Metadata,
}

/// Deterministic per-bundle proof item summary.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustProofItemSummary {
    pub total: u32,
    pub proof_fns: u32,
    pub lemmas: u32,
    pub unsupported: u32,
}
