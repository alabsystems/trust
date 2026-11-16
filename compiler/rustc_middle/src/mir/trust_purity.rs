// Trust: the per-body fact the Clean-origin purity guard reads.
//
// Produced by the `trust_rust_purity_fact` query (provider in
// `rustc_mir_transform::clean_origin_mir`) from a body's PRE-STEAL elaborated MIR, and
// consumed only by that module's purity walk. The type lives here because the fact is a
// disk-cached, arena-allocated query result. It holds NO MIR: the callees to walk and one
// flag.

use rustc_hir::def_id::DefId;
use rustc_macros::{StableHash, TyDecodable, TyEncodable};

/// Trust: what the purity guard learns from one Rust body, in the order its walk meets
/// it: the resolved items the body calls, block by block, up to the first thing the guard
/// refuses in the body itself, and whether there is one.
#[derive(Clone, Debug, Default, TyEncodable, TyDecodable, StableHash)]
pub struct TrustPurityFact {
    /// The items (`InstanceKind::Item`) the body's direct calls resolve to, in basic-block
    /// order, up to the first refused statement, terminator or read.
    pub callees: Vec<DefId>,
    /// Whether the body itself is impure after `callees`: a read through a reference
    /// that is not frame-local, a write through a reference, pointer or `static`, a
    /// thread-local reference, a raw pointer, an intrinsic statement other than
    /// `assume`, inline assembly, a destructor, or a call the guard cannot resolve to an
    /// item (a function pointer, a `dyn` method, a shim, an intrinsic).
    pub impure: bool,
}
