// Trust: what the `trust_ir_of` query returns (spawn census plan step P4, design
// `docs/design/2026-09-29-spawn-census-by-construction.md` §5.2 and §10 step 6).
//
// The direct THIR -> trust-ir producer emits one `trust_ir::Module` per body. That module
// does not name its callees: an emitted `Inst::Call { callee }` / `Constant::FnDef` carries a
// dense BODY-LOCAL `FuncId` (`1..`, the body itself is `functions[0]`), and the identity behind
// each id lives in the producer's callee ledger (`trust_thir_lower::CalleeRef`). A consumer
// that reads the module alone sees calls into nothing. This type carries the module together
// with the projection of that ledger a consumer can use, and with what the producer knows the
// module does NOT carry of the program, so that "absent from the module" is never read as
// "absent from the program". It holds no MIR and grants no authority; the census's trust-ir
// lane (`trust_thir_lower::spawn_census`) is its consumer.
//
// The ledger type itself cannot cross the query boundary: it lives in the producer's crate,
// which depends on this one, and the producer's frozen files (`lineage.rs` digests it field by
// field) fix its shape. The projection below is what the producer already computes, no more.

use rustc_hir::def_id::DefId;

/// Trust: one body's direct THIR -> trust-ir lowering, with the identity of every callee id
/// it emits (see the module comment).
#[derive(Debug)]
pub struct TrustIrBody {
    /// The per-body module: the body is `functions[0]`; any further function is a
    /// producer-synthesized closure -> fn-pointer adapter the body names.
    pub module: trust_ir::Module,
    /// One row per body-local callee `FuncId` the producer admitted, in admission order. A
    /// `FuncId` the module references that no row names is unledgered: nothing is known of it.
    pub callees: Vec<TrustIrCallee>,
    /// What the producer did not model of the program in this body, beyond what the module
    /// itself spells as unknown (a value-less global, an `Inst::Drop` the census cannot
    /// resolve). Empty means the producer claims the module carries every call, drop and
    /// callable value of the body; that claim is the producer's (design §12, R7).
    pub omissions: Vec<TrustIrOmission>,
}

/// Trust: the identity behind one body-local callee `FuncId` (a projection of
/// `trust_thir_lower::CalleeRef`).
#[derive(Clone, Debug)]
pub struct TrustIrCallee {
    /// The id exactly as emitted into `Inst::Call { callee }` / `Constant::FnDef`.
    pub func_id: trust_ir::FuncId,
    /// The callee's assembly identity: the resolved item for a concrete call, the trait
    /// method for a `dyn` dispatch or an unresolved call.
    pub def_id: DefId,
    /// The edge names one concrete instance (`CalleeRef::concrete_key` is `Some`).
    pub concrete: bool,
    /// The edge must stay bodyless (`CalleeRef::force_havoc`). With `concrete`, the instance
    /// has no body of its own here (a generic callee's instance, a shim); without it, the edge
    /// is a HAVOC: a call the producer did not resolve to one instance (a call through type
    /// parameters or an opaque type, a `dyn` dispatch, a resolution that selected nothing).
    /// The ledger does not say which, and one row may stand for several such calls.
    pub force_bodyless: bool,
    /// The callee's declared parameter types, from `tcx.fn_sig`, in this body's module
    /// tables; `None` when the producer could not sign it.
    pub params: Option<Vec<trust_ir::Ty>>,
}

/// Trust: a fact of the program the body's module does not carry, by the producer's own
/// account.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrustIrOmission {
    /// The drop planner refused the body, so the producer emitted none of its drops: the
    /// destructors the program runs are not in the module (the reason is the planner's).
    ElidedDrops(String),
    /// A capture-free closure was passed to a call as the `()` placeholder: the callable
    /// value is not in the module.
    ClosureValueAsUnit,
    /// A named constant is a placeholder the crate finalizer patches later, at a type that
    /// may hold a callable: its value is not in the module.
    PendingConstValue,
}
