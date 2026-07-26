//! Trust: Compiler-native Trust contract IR.
//!
//! This module is the first query-facing contract model inside rustc. It is
//! deliberately independent from parser/lowering and from the external
//! `trust-types` crate: later passes can translate source attributes, MIR
//! assertions, or inferred facts into this typed bundle without making the
//! query API depend on any one frontend representation.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_macros::{StableHash, TyDecodable, TyEncodable};
use rustc_span::{Span, Symbol};

use crate::mir::{BasicBlock, Local};
use crate::ty::{Ty, TyCtxt};

rustc_index::newtype_index! {
    /// Dense per-function index for Trust contracts.
    #[stable_hash]
    #[encodable]
    #[orderable]
    #[debug_format = "TrustContractId({})"]
    pub struct TrustContractId {}
}

/// Per-function Trust contracts exposed through the query system.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustContractBundle<'tcx> {
    /// Function or item this bundle describes.
    pub def_id: DefId,

    /// Contracts attached to this function, indexed by `TrustContractId`.
    pub contracts: IndexVec<TrustContractId, TrustContract<'tcx>>,

    /// Trust: first-class loop clauses (E4 `invariant` / E5 `decreases`),
    /// kept OUT of the dense `contracts` index deliberately — downstream
    /// consumers reconstruct stable ids from that index, and fn-level
    /// consumers must keep converting even when loop clauses are present.
    /// Every clause here is authored spec: a consumer that cannot discharge
    /// it must surface it (report note / grade impact), never drop it.
    pub loop_contracts: Vec<TrustContract<'tcx>>,

    /// Small deterministic summary for quick callers and diagnostics.
    pub summary: TrustContractSummary,
}

impl<'tcx> TrustContractBundle<'tcx> {
    /// Build the current empty scaffold bundle for an item.
    #[must_use]
    pub fn empty(def_id: DefId) -> Self {
        Self {
            def_id,
            contracts: IndexVec::new(),
            loop_contracts: Vec::new(),
            summary: TrustContractSummary::default(),
        }
    }

    /// Returns true when no Trust contracts are available for this item.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty() && self.loop_contracts.is_empty()
    }

    /// Total number of function and loop contracts in this bundle.
    #[must_use]
    pub fn len(&self) -> usize {
        self.contracts.len() + self.loop_contracts.len()
    }

    /// Iterate over every authored contract without making callers remember
    /// that loop clauses use a separate, non-dense storage lane.
    pub fn iter_all(&self) -> impl Iterator<Item = &TrustContract<'tcx>> {
        self.contracts.iter().chain(self.loop_contracts.iter())
    }

    /// Trust: cheap pre-filter for the `trust_contracts` query — true only for
    /// a body owner whose HIR body carries first-class contract clauses. Both
    /// the query provider and the metadata encoder gate on this, so the query
    /// (dep node, arena allocation, disk-cache row) only ever executes for
    /// items that actually have contracts — keeping the query's "only invoked
    /// for items that have contracts" disk-cache contract true.
    #[must_use]
    pub fn def_may_have_contracts(tcx: TyCtxt<'tcx>, local_def_id: LocalDefId) -> bool {
        matches!(tcx.def_kind(local_def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Closure)
            && tcx.opt_hir_owner_nodes(local_def_id).is_some()
            && tcx.hir_maybe_body_owned_by(local_def_id).is_some_and(|body| body.contract.is_some())
    }

    /// Lookup a contract by dense id.
    #[must_use]
    pub fn contract(&self, id: TrustContractId) -> Option<&TrustContract<'tcx>> {
        self.contracts.get(id)
    }
}

/// One Trust contract clause after conversion into compiler-native form.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustContract<'tcx> {
    /// Trust: the parser-canonicalized `by <thm>` citation identity and exact
    /// authored span (E9). The current kernel result is an advisory statement
    /// match only: it never discharges or grades a Rust/Trust-IR VC. Authority
    /// remains hard-blocked until the theorem and typed goal are digest-bound
    /// to the canonical direct-frontend Trust-IR obligation.
    pub citation: Option<TrustContractCitation>,
    /// What semantic role this clause plays.
    pub kind: TrustContractKind,

    /// Where this contract came from.
    pub source: TrustContractSource,

    /// Program point or scope this contract constrains.
    pub subject: TrustContractSubject,

    /// Typed predicate payload. Initially this can remain opaque while
    /// parser/lowering integration lands.
    pub predicate: TrustContractPredicate<'tcx>,

    /// Source span for diagnostics.
    pub span: Span,

    /// Keyword span for native loop clauses. Function/attribute contracts do
    /// not currently retain a separate keyword token and use `None`.
    pub keyword_span: Option<Span>,
}

/// One authored Clean theorem citation carried intact through the compiler's
/// contract query boundary. Keeping the canonical name and source span in one
/// value prevents metadata/query consumers from accidentally retaining the
/// semantic identity while dropping diagnostic attribution. This record does
/// not itself confer proof authority.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustContractCitation {
    /// Parser-canonicalized dotted declaration name.
    pub name: Symbol,
    /// Exact authored `by <thm>` span, distinct from the predicate span used
    /// to recover and elaborate the clause goal.
    pub span: Span,
}

/// Contract roles understood by the compiler query boundary.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractKind {
    /// Function precondition (`#[requires(...)]`).
    Requires,
    /// Function postcondition (`#[ensures(...)]`).
    Ensures,
    /// Type or value invariant.
    Invariant,
    /// Loop invariant.
    LoopInvariant,
    /// Well-founded function-recursion or loop termination measure
    /// (`decreases e`, two-language design E5 — one termination surface per
    /// function or loop).
    Decreases,
    /// Assumption available to verification only.
    Assumes,
    /// Assertion that must be proved.
    Asserts,
    /// Refinement relation between implementation and specification.
    Refinement,
    /// Temporal/liveness property.
    Temporal,
}

/// Origin of a contract clause.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractSource {
    /// User-written source attribute.
    Attribute,
    /// Compiler-native signature clause (`fn f(..) requires P ensures Q`).
    Native,
    /// Compiler-generated contract for a built-in operation.
    Builtin,
    /// Inferred by compiler analysis.
    Inferred,
    /// Synthesized by a Trust pass.
    Synthesized,
}

/// Scope or MIR point constrained by a contract.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractSubject {
    /// Whole-function contract.
    Function,
    /// Contract anchored at a loop header.
    Loop { header: TrustMirLocation },
    /// Contract anchored at a source/HIR loop whose MIR location is not yet
    /// resolved. `id` is unique within the enclosing function; spans provide
    /// honest full-loop and header-only source information but are never used
    /// as identity keys.
    HirLoop { id: TrustLoopId, loop_span: Span, header_span: Span },
    /// Contract anchored at a specific MIR statement or terminator boundary.
    Mir { location: TrustMirLocation },
}

/// Stable per-function source-loop identity used by contract metadata before
/// a sound HIR-to-MIR loop-header mapping exists.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustLoopId {
    pub index: u32,
}

/// Query-safe MIR location for contract anchors.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustMirLocation {
    /// Basic block containing the contract anchor.
    pub block: BasicBlock,
    /// Statement index within `block`; the terminator is represented by the
    /// statement count of that block.
    pub statement_index: u32,
}

/// A typed Trust contract payload.
#[derive(Clone, Debug, TyEncodable, TyDecodable, StableHash)]
pub struct TrustContractPredicate<'tcx> {
    /// The payload's type/domain tag at the compiler-query boundary.
    ///
    /// Attribute contracts are ordinary HIR expressions and therefore carry
    /// their compiler-owned Rust type. Native clauses live in the verifier
    /// parser island: their spelling is not a Rust HIR expression, so claiming
    /// a Rust `Ty` for it would be unsound. Those clauses carry the verifier
    /// sort required by their clause kind (`Bool` for predicates, `Int` for a
    /// `decreases` measure). The tag is not, by itself, validation evidence:
    /// always-on E4/E5 admission establishes it, while another native clause
    /// may still be represented as unsupported/opaque.
    pub ty: TrustContractPayloadType<'tcx>,

    /// The current compiler-native expression shape.
    pub kind: TrustContractPredicateKind,
}

/// Honest type carrier for one compiler-query contract payload.
///
/// `Rust` means rustc type-checked an actual HIR expression. `Verifier` records
/// the sort required by the native clause kind; consumers must still inspect
/// the predicate/admission result and must not treat the tag as evidence that
/// rustc or the verifier elaborator type-checked the authored snippet.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractPayloadType<'tcx> {
    Rust(Ty<'tcx>),
    Verifier(TrustContractVerifierSort),
}

impl<'tcx> From<Ty<'tcx>> for TrustContractPayloadType<'tcx> {
    fn from(ty: Ty<'tcx>) -> Self {
        Self::Rust(ty)
    }
}

// Preserve the common read-only comparison used by existing query clients
// without making a verifier-only sort masquerade as a Rust type.
impl<'tcx> PartialEq<Ty<'tcx>> for TrustContractPayloadType<'tcx> {
    fn eq(&self, other: &Ty<'tcx>) -> bool {
        matches!(self, Self::Rust(ty) if ty == other)
    }
}

/// Expected result sorts imposed by native verifier-language clause kinds.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractVerifierSort {
    Bool,
    Int,
}

/// Query-owned structural proposition for a compiler-lowered contract.
///
/// This deliberately contains only the closed expression vocabulary that the
/// compiler can lower losslessly into `trust_types::Formula`. The authored
/// spelling remains alongside it in [`TrustContractPredicateKind::Typed`] for
/// diagnostics and Clean elaboration, but it is never the semantic carrier:
/// every consumer must use this tree and must fail closed if the spelling does
/// not round-trip to the same structure.
#[derive(Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractProposition {
    Bool(bool),
    Int(i128),
    UInt(u128),
    Var { name: Symbol, domain: TrustContractPropositionDomain },
    Not(Box<Self>),
    And(Vec<Self>),
    Or(Vec<Self>),
    Implies(Box<Self>, Box<Self>),
    Eq(Box<Self>, Box<Self>),
    Lt(Box<Self>, Box<Self>),
    Le(Box<Self>, Box<Self>),
    Gt(Box<Self>, Box<Self>),
    Ge(Box<Self>, Box<Self>),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Rem(Box<Self>, Box<Self>),
    Neg(Box<Self>),
}

/// Exact source-domain identity for a free variable in a compiler-owned
/// proposition. The downstream VC logic may intentionally model primitive
/// integers as mathematical integers, but that abstraction must not erase the
/// Rust signature used to authorize an executable monitor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractPropositionDomain {
    Bool,
    /// A compiler-synthesized mathematical carrier (for example an enum
    /// discriminant abstraction), not a primitive Rust integer.
    MathematicalInt,
    /// A target-width Rust integer. Keeping this distinct from a fixed-width
    /// integer prevents (for example) `usize` and `u64` from acquiring the
    /// same proposition identity on a 64-bit target.
    PointerSizedInt { width: u32, signed: bool },
    MachineInt { width: u32, signed: bool },
}

/// First-stage predicate representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustContractPredicateKind {
    /// A structurally typed proposition plus its canonical authored spelling.
    /// The tree, not `text`, is the authority consumed by static verification.
    Typed { text: Symbol, proposition: TrustContractProposition },
    /// Opaque textual contract body interned as a symbol.
    Opaque { text: Symbol },
    /// Predicate is represented by a MIR local value.
    MirLocal { local: Local },
    /// Literal boolean predicate.
    BoolLiteral { value: bool },
    /// Placeholder for contracts the frontend found but cannot yet lower.
    Unsupported { reason: Symbol },
}

/// Deterministic per-bundle summary.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustContractSummary {
    /// Total contracts in the bundle.
    pub total: u32,
    /// Number of preconditions.
    pub requires: u32,
    /// Number of postconditions.
    pub ensures: u32,
    /// Number of invariants, including loop invariants.
    pub invariants: u32,
    /// Number of function-recursion and loop termination measures
    /// (`decreases` clauses, E5).
    pub decreases: u32,
    /// Number of assertion contracts.
    pub assertions: u32,
    /// Number of contracts retained as opaque or unsupported payloads.
    pub opaque: u32,
}
