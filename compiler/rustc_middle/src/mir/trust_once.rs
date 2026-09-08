// Trust: per-body facts for the once-initializer re-entrancy check.
//
// Produced by the `trust_mir_once_body_facts` query (provider in
// `rustc_mir_transform::trust_once_reentrancy`) and consumed only by that
// module's whole-crate walk. The types live here because the facts are a
// disk-cached, arena-allocated query result. They hold NO MIR: a `LocalDefId`
// per cell/edge, a `Symbol` per method, and a `Span` per wait site.

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_macros::{StableHash, TyDecodable, TyEncodable};
use rustc_span::{Span, Symbol};

/// Trust: which Once-family cell a local `static` IS — its exact type, no
/// peeling. A cell behind a reference, inside a struct field, or wrapped in a
/// `thread_local!` `LocalKey` is not a census entry (documented false
/// negatives of the check).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub enum TrustOnceCellKind {
    /// `std::sync::OnceLock`: a re-entrant wait parks the initializing thread forever.
    OnceLock,
    /// `std::sync::LazyLock`: the same `Once` underneath — a re-entrant wait deadlocks.
    LazyLock,
    /// `std::sync::Once`: a re-entrant wait deadlocks.
    Once,
    /// `core::cell::OnceCell`: a re-entrant wait panics (`reentrant init`).
    OnceCell,
    /// `core::cell::LazyCell`: the cell is poisoned while its initializer runs, so a
    /// re-entrant wait panics.
    LazyCell,
}

impl TrustOnceCellKind {
    /// `true` for the `std::sync` kinds, whose re-entry is a deadlock; `false` for the
    /// `core::cell` kinds, whose re-entry is a panic.
    pub fn deadlocks(self) -> bool {
        matches!(self, Self::OnceLock | Self::LazyLock | Self::Once)
    }

    /// The `Lazy*` kinds carry their initializer in the `static` itself.
    pub fn is_lazy(self) -> bool {
        matches!(self, Self::LazyLock | Self::LazyCell)
    }

    /// The type's path as users write it.
    pub fn path(self) -> &'static str {
        match self {
            Self::OnceLock => "std::sync::OnceLock",
            Self::LazyLock => "std::sync::LazyLock",
            Self::Once => "std::sync::Once",
            Self::OnceCell => "core::cell::OnceCell",
            Self::LazyCell => "core::cell::LazyCell",
        }
    }
}

/// Trust: one call in one body that WAITS on a local Once-family cell
/// `static` — a call that parks (or panics) if the cell is being initialized
/// by the calling thread at that moment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable, StableHash)]
pub struct TrustOnceWaitSite {
    /// The `static` the call waits on.
    pub cell: LocalDefId,
    /// The cell's kind (always equal to the cell's census kind).
    pub kind: TrustOnceCellKind,
    /// The waiting method's name (`get_or_init`, `deref`, `force`, ...), for rendering.
    pub method: Symbol,
    /// The call's `fn_span`.
    pub span: Span,
    /// The body this call STARTS as the cell's initializer, when the method takes one
    /// and the argument's type names a closure or a fn item. `None` for a pure wait
    /// (`wait`, `set`, `deref`, ...) or an opaque initializer (`fn` pointer, `dyn`).
    pub initializer: Option<DefId>,
}

/// Trust: everything the re-entrancy walk needs from one body, without the body.
#[derive(Clone, Debug, Default, TyEncodable, TyDecodable, StableHash)]
pub struct TrustOnceBodyFacts {
    /// Every wait on a local cell static, in basic-block order.
    pub waits: Vec<TrustOnceWaitSite>,
    /// Local fn items this body passes as call ARGUMENTS to a non-spawning call. A
    /// callee may invoke such a value synchronously, so the walk treats each as an
    /// edge (the adjacency query `trust_mir_direct_local_callees` already treats
    /// closure-typed arguments that way; fn items are added here). Sorted, deduped.
    pub fn_value_edges: Vec<LocalDefId>,
    /// Local closures and fn items this body hands to a `std::thread` spawn entry
    /// point. They run on ANOTHER thread, so they are subtracted from the walk's
    /// edges: a spawned thread waiting on the cell is not a self-wait. Sorted, deduped.
    pub spawned: Vec<LocalDefId>,
}
