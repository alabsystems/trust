//! trust-thir-lower: lower source (THIR) **directly to trust-ir** — the front end of the
//! inverted pipeline (P1), with trust-ir as the hub.
//!
//! `THIR -> trust_ir::Module` is the PRIMARY structural lowering. From the `Module`, native
//! codegen (trust-cg) and the LLVM-compat MIR shim (`trust-ir -> MIR`) descend. Direct
//! verification is still a capability boundary: this producer does not yet attach source
//! contracts or proof obligations, so its module/differential/dump is not proof authority and
//! cannot produce a native verification request. Authenticated MIR-derived evidence temporarily
//! preserves compatibility and differential coverage while that direct binding is completed;
//! MIR is neither the canonical semantics nor the end-state frontend. `VerifiableFunction`/MIR
//! are otherwise derived views (here only as the `differential` oracle). See
//! `docs/DESIGN-P1-ir-inversion.md`, `docs/FUSION.md`.
//!
//! Toward a **Rust-free Trust toolchain**: rustc's THIR (front end) and the MIR/LLVM path are
//! removable scaffolding; this crate begins moving the center of gravity onto trust-ir.
//!
//! STATUS: real lowering of a multi-block subset — literals, binary arithmetic, signed/unsigned
//! comparisons (`ICmp`), `let` bindings + parameter refs, block statements, `if`/`else` lowered to a
//! genuine CFG (`CondBr` + arm blocks + a join block carrying the if-result as a block-param), the
//! short-circuit operators `&&`/`||` (`ExprKind::LogicalOp`, desugared to the same `if`-shaped CFG —
//! `a && b ≡ if a { b } else { false }`, `a || b ≡ if a { true } else { b }`), MUTABLE LOCALS via SSA
//! value-versioning (`let mut y = init; …; y = expr; …; y` — a use reads the local's current
//! `ValueId`, an `ExprKind::Assign` to a local rebinds it, and a local reassigned inside an `if` OR
//! `match` arm merges across the join through an added block-parameter, the same merge
//! `if`/`&&`/`||`/`match` use for an expression's value, generalized to also carry every local
//! mutated since the split), COMPOUND ASSIGNMENT (`ExprKind::AssignOp` — `x += e`, `x /= e`, …,
//! lowered as the MIR-faithful read-binop-write on a bare/promoted local or a `*r`-deref place,
//! sharing `emit_arith_binop` with `ExprKind::Binary`), MIR-FAITHFUL ARITHMETIC SAFETY CHECKS
//! (`emit_arith_binop` mirrors rustc's `build_binary_op` exactly: `+`/`-`/`*` →
//! `Inst::Overflow` + overflow `Assert` under `overflow_checks`; `/`/`%` → an UNCONDITIONAL
//! divisor-nonzero `Assert` plus, for signed ints, the unconditional `MIN / -1` overflow `Assert`;
//! `<<`/`>>` → a shift-amount-in-range `Assert` under `overflow_checks`; each `Assert` carries the
//! same `ProofAnnotation` the MIR-side bridge attaches — `NoOverflow`/`DivNonZero`/`ShiftInRange`),
//! NAMED CONSTANTS (`ExprKind::NamedConst` — `i32::MAX`, user `const` items, associated consts —
//! and inline `ExprKind::ConstBlock`, const-evaluated via `const_eval_resolve_for_typeck` and
//! admitted as faithfully typed scalar constants or recursively decoded tuple/array/struct/enum
//! aggregates; LOCAL consts are deferred — a sentinel placeholder + `PendingConst` record the
//! `crate_module` finalizer evaluates and patches at the reentrancy-safe `analysis` seam), CALLS
//! (`Inst::Call` for direct free fns AND for
//! method/operator calls resolved to a concrete `InstanceKind::Item` via
//! `ty::Instance::try_resolve`, INCLUDING the rust-call untupled `Fn`/`FnMut::call{,_mut}` on a
//! non-capturing local closure (`CalleeKind::ClosureCall` — env rebuilt as a fresh unit-slot
//! Ptr, tupled args split element-wise) — generic/dyn/trait-default/shim/capturing-closure
//! shapes keep precise split fail-closed tags; `Inst::CallIndirect` + a ledgered
//! `Constant::FnDef` for
//! first-class fn-pointer calls in the reify→call fragment; borrow-ptr call ARGS admitted with
//! the Freeze-scalar-snapshot / promoted-slot proofs in `lower_call_args`), MATCH on integer,
//! CHAR (first-class `Ty::Char`, using an unsigned 32-bit code-point carrier),
//! BOOL (a `CondBr`, built MIR's bool-`SwitchInt` shape — `lower_bool_match`), simple-enum, and
//! TUPLE (irrefutable single-arm destructure via `ExtractField` — `lower_tuple_match`)
//! scrutinees, CONST/STATIC INITIALIZER bodies (`BodyTy::Const` → a zero-param function
//! returning the initializer value, `lower_const_body`; marked `BodyKind::ConstInit`/
//! `StaticInit` so the flip refuses them and `crate_module` records/marks them), and
//! tail/explicit `Return`. Everything else is fail-closed `unsupported` (the migration ratchet). The
//! `differential` oracle proves *semantic* equivalence against the MIR-side trust-ir by sampled
//! interpretation. `crate_module` makes the per-body output CONSUMABLE (P1 Phase 0): a thread-safe
//! registry collects every body's `Lowered` at the `mir_built` hook, and a crate-level finalizer
//! (rustc_interface `analysis` seam) assembles ONE deterministic `trust_ir::Module` — intra-crate
//! callee `FuncId`s resolved, extern/ambiguous callees fail-closed as bodyless declarations — and
//! dumps it (binary codec + canonical text + `coverage.json`) when
//! `-Z trust-dump=ir:<dir>` is set. The sidecar carries a machine-readable
//! `direct_obligation_capability` marker so automation cannot promote structural parity to a
//! verification claim.
//! `rustc_private` → builds ONLY via `x.py build/check`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: Apache-2.0

#![feature(rustc_private)]
#![allow(internal_features)]
#![allow(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_ir;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_ast::LitKind;
use rustc_middle::middle::region;
// Trust: the compound-assignment operator kind (`+=`, `/=`, …) carried by `ExprKind::AssignOp`;
// `MirBinOp::from(op)` recovers the underlying binary op (the exact conversion rustc's own
// `stmt_expr` AssignOp lowering uses via `op.into()`).
use rustc_middle::mir::AssignOp as MirAssignOp;
use rustc_middle::mir::{BinOp as MirBinOp, UnOp as MirUnOp};
use rustc_middle::thir::{
    ArmId, BodyTy, Expr, ExprId, ExprKind, LocalVarId, LogicalOp, Pat, PatKind, StmtId, StmtKind,
    Thir,
};
// Trust: the array-to-slice unsizing coercion kind (`PointerCoercion::Unsize`) the slice fat-pointer
// lowering matches on (the `ExprKind::PointerCoercion` arm).
use rustc_middle::ty::adjustment::PointerCoercion;
// Trust: `TypeVisitableExt` supplies `has_non_region_param`/`has_non_region_infer`, the guards the
// `NamedConst`/`ConstBlock` const-eval path checks before calling `const_eval_resolve_for_typeck`
// (which `bug!`s on inference vars and cannot resolve still-generic args).
use rustc_middle::ty::{self, Ty as RustcTy, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
// Trust: `ProofAnnotation` — the advisory proof marker the MIR-side bridge attaches to its asserts
// (`assert_proof_annotation` in crates/trust-ir-bridge/src/lower.rs); the producer attaches the SAME
// kinds (`NoOverflow`/`DivNonZero`/`ShiftInRange`) so both front-ends agree structurally.
use trust_ir::proof::ProofAnnotation;
// Trust (wave-16): `GlobalId` is defined in `trust_ir::value` and not re-exported at the crate
// root (unlike the other typed ids), so import it by its canonical path.
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp,
    Block,
    BlockId,
    CastOp,
    Constant,
    FCmpOp,
    FuncId,
    FuncTy,
    FuncTyId,
    Function,
    // Trust (wave-16): promoted-borrow module globals.
    Global,
    ICmpOp,
    Inst,
    InstrNode,
    SourceSpan,
    Linkage,
    Module,
    OverflowOp,
    SwitchCase,
    Ty,
    UnOp,
    ValueId,
};

mod artifact_publication;
pub mod crate_module;
pub mod differential;
pub mod flip;
pub mod flip_registry;
pub mod mir_differential;
pub mod to_mir;

/// Trust (totality Batch B): depth fuel for the `(DefId, args)`-keyed ADT visit stacks
/// (`adt_visit_stack`, `fat_shape`'s `visited`). Per-instantiation keying makes nested
/// DISTINCT instantiations (typenum's `UInt<UInt<..>>` towers) walkable as the finite DAGs
/// they are, but polymorphic recursion behind pointers admits unboundedly many distinct
/// pairs — the fuel bounds the DEPTH, failing closed with the sanctioned `Ty(adt-depth)`
/// tag. 128 comfortably clears typenum's deepest towers (~64 levels for U(2^64)) while
/// keeping the guards' linear stack scans trivial.
const ADT_VISIT_FUEL: usize = 128;

/// Trust: what kind of body was lowered. `Fn` is a function/closure body (`BodyTy::Fn`);
/// `ConstInit`/`StaticInit` are const/static INITIALIZER bodies (`BodyTy::Const`) lowered as
/// zero-parameter functions returning the initializer value (`lower_const_body`). Consumers use
/// this to keep initializer bodies out of function-only lanes fail-closed: the flip registry
/// refuses them (`optimized_mir` is never called for const-context bodies — rustc panics
/// "do not use `optimized_mir` for constants" — but never trust the caller), and `crate_module`
/// records the kind per body (coverage rows + a name marker on spliced initializers).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    Fn,
    ConstInit,
    StaticInit,
}

/// Trust (wave-AR): repeat count at or above which `[c; N]` takes the COMPACT O(N) lowering
/// (one `Inst::Const` over a count-based `Ty::Array(TyId, N)`) instead of the legacy
/// `Ty::Tuple([T; N])` seed + N `InsertField`s, whose memory is O(N^2) (each of the N
/// instructions carries an O(N) `Ty::Tuple`). See `lower_repeat_compact` for the full
/// contract. 1024 sits above every repeat in the existing probe/acceptance corpus (incl. the
/// real-grid PAGE_SIZE=256 fallback copy) — keeping those dumps byte-identical — and below
/// the measured pathological sizes (4096 → 1.4GB legacy; the real `[0; 65536]` → ~100GB).
const REPEAT_COMPACT_MIN: u64 = 1024;

/// Conservative precondition for asking rustc for a layout from the THIR lowering pipeline.
///
/// This producer runs from inside `mir_built`. A layout query for a still-generic, inferred,
/// placeholder-bearing, aliased, or coroutine type can normalize through `type_of`, borrowck, or
/// `coroutine_layout` and re-enter a query currently on the stack, producing E0391/delayed bugs
/// instead of a recoverable `LayoutError`. Escaping bound variables likewise cannot be supplied to
/// the fully-monomorphized typing environment used by these calls, and `CoroutineWitness` is a hard
/// layout bug rather than an ordinary error. Declining the query is fail-closed: callers only lose
/// an optional lowering/flip optimization and never invent a layout.
pub(crate) fn layout_query_is_reentrant_safe(ty: RustcTy<'_>) -> bool {
    !ty.has_non_region_param()
        && !ty.has_non_region_infer()
        && !ty.has_non_region_placeholders()
        && !ty.has_aliases()
        && !ty.has_coroutines()
        && !ty.has_escaping_bound_vars()
        && !ty
            .walk()
            .filter_map(|arg| arg.as_type())
            .any(|inner| matches!(inner.kind(), ty::CoroutineWitness(..)))
}

/// A lowered `trust_ir::Module` plus the fail-closed coverage report (the migration ratchet).
pub struct Lowered {
    pub module: Module,
    /// Trust: fn body vs const/static initializer body (see [`BodyKind`]).
    pub body_kind: BodyKind,
    /// Trust (totality Batch C): true iff the body reads at least one SYMBOLIC assoc
    /// const (a value-less extern-immutable global — see `LowerCx::symbolic_consts`).
    /// Consumers MUST check this at their seams: the interpretation differential skips
    /// the body as a precise NotRun class (a value-less `Load` interpreted would
    /// manufacture a false TypeError verdict), and the crate-module assembler excludes
    /// it from the executable splice. Checked, never inferred from oracle failure.
    pub symbolic: bool,
    /// THIR shapes not lowered yet: `(span_debug, what)`. Non-empty ⇒ differential gate not green.
    pub unsupported: Vec<(String, &'static str)>,
    /// True if the body emitted any `Inst::Call` or `Inst::CallIndirect`. The callee is a
    /// cross-module `FuncId` (or a dynamic fn-pointer value) the single-function interpreter
    /// cannot resolve, so the differential oracle skips such bodies as coverage-only rather
    /// than asserting a vacuous "both errored at the call" agreement.
    pub contains_call: bool,
    /// Trust (B3-2c seam guard): true iff any call arg used a PLACE-PATH VALUE
    /// CARRIER (the wave-RS/wave-MC/receiver-value fallbacks: a non-pointer
    /// receiver VALUE standing in for a `&`/`&mut` place — sound ONLY under the
    /// CLEAN-ONLY contract, never interpreted). The B9-A seam links local
    /// callees and interprets `contains_call` bodies, which BROKE that contract
    /// latently (unmasked when oracle ZST-ctor coverage opened): the carrier arg
    /// hits the callee's real ptr param as a signature mismatch and mints a
    /// manufactured THIR-defect verdict. The seam skips carrier bodies.
    pub place_path_carrier: bool,
    /// Trust: identity ledger for every callee `admit_callee` admitted — direct free-fn callees,
    /// resolved method/operator callees, and reified fn-pointer targets (`Constant::FnDef`) alike.
    /// The emitted `Inst::Call { callee }` / `Constant::FnDef` `FuncId` is DefIndex-derived, so on
    /// its own it cannot distinguish a local def (resolvable at crate-level assembly) from a
    /// cross-crate def whose index happens to collide with the local index space. `crate_module`
    /// uses this ledger to rewrite intra-crate callee `FuncId`s and to fail-closed (bodyless
    /// declaration) on extern/ambiguous ones.
    pub callees: Vec<CalleeRef>,
    /// Trust: LOCAL consts deferred to the crate finalizer (see [`PendingConst`]). Evaluating a
    /// local const from inside the `mir_built` hook re-enters this crate's MIR building (E0391
    /// cycles, a CTFE type-const ICE, a swallowed hook tail — see `lower_named_const`), so the
    /// body instead carries a PLACEHOLDER `Inst::Const` per entry and the `crate_module`
    /// finalizer — running at the `rustc_interface` `analysis` seam, where every body's MIR is
    /// already built and const eval is reentrancy-safe — patches in the real value before dump.
    /// Non-empty ⇒ the module is NOT yet executable ("pending-const" body): both differentials
    /// must skip it (a placeholder is never interpreted), and splicing without a successful
    /// finalizer patch is forbidden.
    pub pending_consts: Vec<PendingConst>,
}

/// Trust: one LOCAL const the hook could not safely evaluate (reentrancy), deferred to the
/// crate finalizer. The body carries a placeholder
/// `Inst::Const { ty: <mapped int/bool ty>, value: Constant::PhantomData }` — a bare
/// `PhantomData` under a scalar type is ill-typed and emitted NOWHERE else by the producer
/// (the fat-pointer seed only nests it inside a `Constant::Aggregate`), so it doubles as a
/// structurally-unmistakable sentinel the finalizer tripwire can scan for. All fields are
/// plain owned/`Copy` data (`DefId`/`Span` are lifetime-free), so the record survives into
/// `crate_module`'s `'static` registry. The `GenericArgsRef` is deliberately NOT stored
/// (tcx-interned, lifetime-bound): the deferral is only taken when the use-site args are
/// ALL-REGION, which the finalizer re-derives losslessly via
/// `GenericArgs::identity_for_item` + region erasure (regions never affect a const's value).
#[derive(Clone, Debug)]
pub struct PendingConst {
    /// The placeholder instruction's result `ValueId` — the patch key (unique per body in SSA).
    pub value: ValueId,
    /// The local const's `DefId` (`is_local()` held at the deferral site).
    pub def_id: rustc_span::def_id::DefId,
    /// The use-site span, passed to the finalizer's `const_eval_resolve_for_typeck` for
    /// error attribution (lifetime-free: spans are session-global interned indices).
    pub span: rustc_span::Span,
    /// True iff the const's type is `bool` (then `signed`/`bits`/`is_float` are irrelevant).
    pub is_bool: bool,
    /// Trust (wave-8b): true iff the const's type is `f32`/`f64`. Then `signed` is false and
    /// `bits` is the IEEE width (32/64) — the finalizer reinterprets the const's bits into the
    /// f64 carrier (`Constant::Float`) instead of `sign_extend`ing to a `Constant::Int`.
    pub is_float: bool,
    /// Signedness of the integer type (drives the finalizer's `sign_extend`; false for float).
    pub signed: bool,
    /// Mapped fixed width in bits (isize/usize already platform-resolved by `map_ty`; the IEEE
    /// width 32/64 for a float); the finalizer cross-checks it against the re-derived rustc type
    /// (tripwire, fail-closed).
    pub bits: u32,
    /// Trust (B7): true iff the const's type is a COMPOSITE (tuple/array/struct/enum). Then the
    /// scalar shape fields above are all false/0 and the finalizer decodes the CTFE branch
    /// valtree recursively against the placeholder node's mapped `Ty` + the body's registered
    /// struct/enum tables (`eval_pending_const`'s composite leg) instead of the scalar tail.
    pub composite: bool,
}

/// Trust: the identity behind one DefIndex-derived callee `FuncId` (see `Lowered::callees`).
#[derive(Clone, Debug)]
pub struct CalleeRef {
    /// The `FuncId` exactly as emitted into `Inst::Call { callee }`.
    pub func_id: FuncId,
    /// Whether the callee `DefId` is in the crate being compiled (only then is it resolvable).
    pub is_local: bool,
    /// The callee's `DefIndex` (`func_id.index()` by construction; kept explicit for clarity).
    pub def_index: u32,
    /// Trust (wave-6, shim calls): the FULL callee `DefId` — lifetime-free (`PendingConst`
    /// precedent), so the record survives into the `'static` registries. `def_index` alone
    /// cannot rebuild a CROSS-CRATE callee's identity (the krate is lost); the shim's
    /// `Inst::Call` lowering (`to_mir`) resolves the ledgered `FuncId` back to THIS `DefId`
    /// to spell the `TerminatorKind::Call` func operand exactly as built MIR does.
    pub def_id: DefId,
    /// `tcx.def_path_str` of the callee — deterministic, human-readable identity for coverage
    /// records and for the fail-closed extern declaration's name.
    pub def_path: String,
    /// Trust (wave-20): FORCE this callee edge to a bodyless HAVOC declaration at crate assembly,
    /// even if its `DefIndex` has a clean local body. Set for a GENERIC (`has_non_region_param`)
    /// call site — the callee is polymorphic, so linking it to the callee's IDENTITY-lowered body
    /// (which `crate_module::resolve_callee` would do for a local DefIndex) is BOTH an identity lie
    /// AND re-opens the wave-19 DST hole at generic sites (`sig_shapes_coherent` is inert there —
    /// it returns before resolution, and with param args every position classifies `Opaque`→skip).
    /// A havoc decl is unconstrained, so no body/ABI is claimed and no fat/thin flip is realizable.
    pub force_havoc: bool,
    /// Trust (wave-C): the SITE-spelled callee `DefId` — EXACTLY what built MIR writes in the
    /// `TerminatorKind::Call` func operand `FnDef(_, _)`. For a free fn / inherent-impl method this
    /// equals `def_id`; for a TRAIT method or an overloaded-operator desugar it is the TRAIT method
    /// `DefId` (the site spelling; resolution to the concrete impl happens at monomorphization, NOT
    /// in MIR — see `to_mir` DIRECT CALLS). The shim spells the func operand + instantiates the sig
    /// at THIS identity; the crate-assembly identity above (`def_id`/`def_index`/`is_local`/
    /// `def_path`/`force_havoc`) is unchanged, so `crate_module` and clean-rate are untouched.
    pub site_def_id: DefId,
    /// Trust (wave-C): a lifetime-free, re-materializable encoding of the SITE `GenericArgs`
    /// (`node_args`, exactly what built spells). `Some(vec![])` is the zero-generic wave-6 case
    /// (byte-identical behavior). `None` ⇒ the args were outside the encodable concrete fragment
    /// (any region/const arg, or a type arg outside `SiteTy`) ⇒ the shim's Call arm fails closed
    /// (the body stays clean-only, never a wrong flip — a non-matching rebuild is caught by the
    /// comparator's `raw_call_channel` FnDef equality, the liveness-not-safety anchor).
    pub site_args: Option<Vec<SiteArg>>,
}

/// Trust (wave-C): a lifetime-free encoding of one `GenericArg` at a concrete-monomorphic call
/// site — re-materialized to an intern-equal `GenericArgsRef` at shim time (`to_mir::rebuild_site_args`).
/// FIRST SLICE: type args only. A lifetime or const arg makes the whole site un-encodable (`None`),
/// so a body with such a callee stays clean-only. Every leaf is `Copy + 'static`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteArg {
    Ty(SiteTy),
    /// Trust (wave-CR): a LIFETIME arg, encoded region-free. A real region cannot be carried
    /// losslessly across the encode/rebuild boundary, but it does not need to be: the shim rebuilds
    /// it as `ReErased`, and the differential's raw-call channel erases regions on BOTH sides before
    /// pinning callee identity (`mir_differential::raw_calls_in_dfs_order`), so a region-only
    /// difference is region-blind (SOUND — region-only-different `FnDef`s codegen identically).
    ErasedRegion,
}

/// Trust (wave-C): a lifetime-free encoding of a concrete type appearing in a site's `GenericArgs`.
/// Only the concrete, region-free fragment is representable; anything else → `encode_ty` returns
/// `None` → the callee is un-encodable → fail closed. A faithful (intern-equal) rebuild is required
/// only for YIELD — a lossy rebuild produces a non-matching `FnDef` that the comparator rejects,
/// so it can only MISS a flip, never make a wrong one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteTy {
    Bool,
    Char,
    Str,
    Int(ty::IntTy),
    Uint(ty::UintTy),
    Float(ty::FloatTy),
    /// struct / enum / union — `did` + every arg (each must itself be a region/const-free type).
    Adt(DefId, Vec<SiteTy>),
    Tuple(Vec<SiteTy>),
    Array(Box<SiteTy>, u64),
    Slice(Box<SiteTy>),
}

/// Trust (wave-C): encode a site's `GenericArgs` (the raw `node_args`) to the lifetime-free form.
/// `None` if ANY arg is a lifetime/const, or any type arg is outside `SiteTy` (fail closed).
fn encode_site_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Option<Vec<SiteArg>> {
    let mut out = Vec::with_capacity(args.len());
    for a in args.iter() {
        match a.kind() {
            ty::GenericArgKind::Type(t) => out.push(SiteArg::Ty(encode_ty(tcx, t)?)),
            // Trust (wave-CR): a LIFETIME arg → `SiteArg::ErasedRegion` (rebuilt as `ReErased`; the
            // raw-call channel erases regions on both sides, so this pins the callee's did+type/const
            // args region-blindly — SOUND, see `SiteArg::ErasedRegion`). A CONST arg is still
            // un-encodable in this slice → fail closed (a later slice adds `SiteArg::Const`).
            ty::GenericArgKind::Lifetime(_) => out.push(SiteArg::ErasedRegion),
            ty::GenericArgKind::Const(_) => return None,
        }
    }
    Some(out)
}

/// Trust (wave-C): encode a concrete type to `SiteTy`, or `None` (fail closed) for anything outside
/// the region/const-free fragment — a `Ref`/`RawPtr`/`FnDef`/`FnPtr`/`Dynamic`/`Closure`/`Param`/
/// `Alias`/`Infer`/const-generic-array/adt-with-a-lifetime-or-const-arg, etc.
fn encode_ty<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>) -> Option<SiteTy> {
    match t.kind() {
        ty::Bool => Some(SiteTy::Bool),
        ty::Char => Some(SiteTy::Char),
        ty::Str => Some(SiteTy::Str),
        ty::Int(i) => Some(SiteTy::Int(*i)),
        ty::Uint(u) => Some(SiteTy::Uint(*u)),
        ty::Float(f) => Some(SiteTy::Float(*f)),
        ty::Tuple(ts) => {
            let mut v = Vec::with_capacity(ts.len());
            for e in ts.iter() {
                v.push(encode_ty(tcx, e)?);
            }
            Some(SiteTy::Tuple(v))
        }
        ty::Slice(el) => Some(SiteTy::Slice(Box::new(encode_ty(tcx, *el)?))),
        ty::Array(el, len) => {
            let n = len.try_to_target_usize(tcx)?;
            Some(SiteTy::Array(Box::new(encode_ty(tcx, *el)?), n))
        }
        ty::Adt(def, args) => {
            // Every arg of the ADT must itself be a region/const-free type (else the rebuild
            // could not reconstruct an intern-equal args list) — fail closed otherwise.
            let mut v = Vec::with_capacity(args.len());
            for a in args.iter() {
                match a.kind() {
                    ty::GenericArgKind::Type(at) => v.push(encode_ty(tcx, at)?),
                    ty::GenericArgKind::Lifetime(_) | ty::GenericArgKind::Const(_) => return None,
                }
            }
            Some(SiteTy::Adt(def.did(), v))
        }
        _ => None,
    }
}

/// Lower the exact THIR snapshot already owned by the `build_mir_inner_impl`
/// hook under `-Z trust-ir-lower`.
///
/// The hook has just obtained this `Thir` and root from `tcx.thir_body(def)` in
/// order to build MIR. Taking that same snapshot here is load-bearing: a second
/// query used to return `Option<Lowered>` and the hook silently skipped the body
/// on `None`, leaving crate finalization unable to distinguish a complete empty
/// result from a missing producer callback. It also redundantly borrowed the
/// same query result. The direct lane now has one infallible handoff after the
/// caller's successful THIR query; unsupported source shapes remain explicit in
/// [`Lowered::unsupported`].
pub fn lower_module_from_thir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &Thir<'tcx>,
    root: ExprId,
) -> Lowered {
    lower_module_inner(tcx, def, thir, root, false)
}

/// Trust (B): provider for the `trust_ir_of` query — THIR -> trust-ir for one body, with
/// dep-graph identity.
///
/// Before this existed the Module was produced only as a SIDE EFFECT of `mir_built` executing,
/// into a Session-owned registry. On an incremental replay where `mir_built` is cache-green
/// nothing ran, so no Module existed and the compiler silently fell back to built MIR. An
/// artifact that vanishes on a warm cache is an overlay, not a path.
///
/// Borrowing THIR here is safe for the same reason the hook's own comment gives: `mir_built`
/// does NOT steal it ("Don't steal here, instead steal in unsafeck"), so a query forced before
/// unsafeck sees it intact. `thir_body` returning `Err` means typeck already failed — decline
/// rather than invent a Module.
///
/// Returns `None` for a body the producer declines. That is not an error and not evidence of
/// anything: the caller falls back to built MIR exactly as before.
pub fn trust_ir_of<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<&'tcx trust_ir::Module> {
    if !tcx.sess.trust_ir_lower_enabled() {
        return None;
    }
    let Ok((thir, root)) = tcx.thir_body(def) else {
        return None;
    };
    // Trust: the same stolen-THIR hazard that sank the flip's recovery arm (41 flag-induced
    // ICEs). A caller that forces this query after unsafeck steals THIR gets `None`, not a
    // panic — fail closed, loudly checkable via the query's own dep edge.
    if thir.is_stolen() {
        return None;
    }
    let thir = thir.borrow();
    let lowered = lower_module_from_thir(tcx, def, &thir, root);
    // A body with unsupported shapes has no usable Module. Strict mode reports that at the hook,
    // where the span and the tag list are; here it is simply "no artifact".
    if !lowered.unsupported.is_empty() {
        return None;
    }
    Some(tcx.arena.alloc(lowered.module))
}

/// Trust (v2 Phase 0b, RFC docs/TRUST_IR_V2.md §4): the COLLECT-ALL second pass. Re-lowers the
/// body on a FRESH context with `collect_all = true` — the failure seams that normally
/// short-circuit sibling subtrees (first bad call arg, …) instead record their tag and CONTINUE
/// walking, so the returned tag vector approaches the body's FULL leaf demand instead of the
/// first-fail prefix. The result is measurement-ONLY: callers may consume the `unsupported` tag
/// vector and MUST discard everything else (the module under collect-all can contain
/// partially-lowered garbage that must never be spliced/flipped/differentialed — the five
/// `unsupported.is_empty()` gates make that structural. The MIR-build hook extracts the tags
/// once and shares the bounded snapshot with tracing and `crate_module::record`).
pub fn lower_module_collect_all_from_thir<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &Thir<'tcx>,
    root: ExprId,
) -> Vec<(String, &'static str)> {
    lower_module_inner(tcx, def, thir, root, true).unsupported
}

fn lower_module_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    thir: &Thir<'tcx>,
    root: ExprId,
    collect_all: bool,
) -> Lowered {
    let mut module = Module::new(tcx.crate_name(def.to_def_id().krate).to_string());

    // Trust (huge-body cap): a body whose THIR expression count is enormous is
    // machine-generated data, not code this fragment can meaningfully lower.
    // Walking it costs O(exprs) trust-ir insts plus differential-interpretation
    // work — measured 1.6GB RSS on unicode-ident's hook alone (5.1GB with the
    // artifact path) before any cap, and still 8x compile time with a uniform
    // 10k cap because the trie tables are CHUNKED into many just-under-cap
    // static initializers. The cap is therefore per-BODY-KIND:
    //   * fn bodies: 10_000 exprs — far beyond any human-written function;
    //   * const/static INITIALIZER bodies: 512 exprs — hand-written consts are
    //     tiny, while element-walking a constant table buys nothing (the
    //     EVALUATED MIR constant is the authoritative form of such data).
    // Fail OPEN with a precise tag (an honest coverage-gap record), never blow up.
    let body_kind_early = match thir.body_type {
        BodyTy::Fn(_) | BodyTy::GlobalAsm(_) => BodyKind::Fn,
        BodyTy::Const(_) => match tcx.def_kind(def) {
            rustc_hir::def::DefKind::Static { .. } => BodyKind::StaticInit,
            _ => BodyKind::ConstInit,
        },
    };
    let thir_expr_cap = match body_kind_early {
        BodyKind::Fn => 10_000,
        BodyKind::ConstInit | BodyKind::StaticInit => 512,
    };
    if thir.exprs.len() > thir_expr_cap {
        return Lowered {
            module,
            body_kind: body_kind_early,
            unsupported: vec![("body".to_string(), "huge body (THIR expr cap)")],
            contains_call: false,
            place_path_carrier: false,
            callees: Vec::new(),
            pending_consts: Vec::new(),
            symbolic: false,
        };
    }
    let mut cx = LowerCx {
        tcx,
        thir,
        // Trust (wave-DP): the current body's identity (accessor-lane gate).
        body_def: def.to_def_id(),
        next_value: 0,
        next_block: 1, // 0 is reserved for the entry block
        blocks: Vec::new(),
        cur: Vec::new(),
        cur_id: BlockId::new(0),
        cur_span: None,
        files: Vec::new(),
        value_names: Vec::new(),
        cur_params: Vec::new(),
        sealed: false,
        locals: Vec::new(),
        local_tys: Vec::new(),
        contains_call: false,
        place_path_carrier: false,
        callees: Vec::new(),
        pending_consts: Vec::new(),
        pending_func_tys: Vec::new(),
        pending_tys: Vec::new(),
        // Trust (B6): first-class closure-type ledger (v25 Fn/ByValue slice).
        pending_closure_tys: Vec::new(),
        // Trust (wave-16): promoted-borrow globals ledger.
        pending_globals: Vec::new(),
        trait_object_ids: Vec::new(),
        // Trust (totality Batch C): symbolic assoc-const ledger.
        symbolic_consts: Vec::new(),
        static_globals: Vec::new(),
        unsupported: Vec::new(),
        collect_all,
        struct_ids: Vec::new(),
        adt_visit_stack: Vec::new(),
        pending_structs: Vec::new(),
        enum_ids: Vec::new(),
        enum_declined: Vec::new(),
        pending_enums: Vec::new(),
        loop_stack: Vec::new(),
        borrow_ptrs: Vec::new(),
        ref_param_ptrs: Vec::new(),
        // Trust (wave-16): promoted-borrow GlobalAddr pointers (return-escape allow-list).
        global_ptrs: Vec::new(),
        // Trust (wave-25b): derived interior-pointer return allow-list (`&self.field` @ offset != 0).
        interior_ptrs: Vec::new(),
        promoted: Vec::new(),
        promoted_slots: Vec::new(),
        promoted_tys: Vec::new(),
        mut_borrow_ptrs: Vec::new(),
        // Trust (wave-ER): opaque-carrier locals ledger (let-chain payload bindings +
        // unregistrable non-pure `&mut` aggregate locals).
        opaque_carrier_locals: Vec::new(),
        // Trust (wave-SEAM): Option-discriminant value-lane ledger (flag-gated).
        option_lane_values: Vec::new(),
        fn_return_rty: None,
    };

    let mut body_kind = BodyKind::Fn;
    match thir.body_type {
        BodyTy::Fn(fn_sig) => cx.lower_fn(&mut module, def, fn_sig, root),
        // Trust: a const/static INITIALIZER body (`BodyTy::Const`) — the MIR view of such a
        // body IS a zero-argument body whose result lands in RETURN_PLACE (`construct_const`),
        // so it lowers as a zero-param function returning the initializer value, with the same
        // expression machinery fn bodies use. `hir_body_owner_kind` routes exactly the
        // const-context owners here (`Const{..}`/`Static(_)` in `thir/cx/mod.rs`); the DefKind
        // gate below is checked, not assumed, so an unexpected owner keeps the precise tag.
        BodyTy::Const(const_ty) => match tcx.def_kind(def) {
            rustc_hir::def::DefKind::Const { .. }
            | rustc_hir::def::DefKind::AssocConst { .. }
            | rustc_hir::def::DefKind::AnonConst
            | rustc_hir::def::DefKind::InlineConst => {
                body_kind = BodyKind::ConstInit;
                cx.lower_const_body(&mut module, def, const_ty, root);
            }
            rustc_hir::def::DefKind::Static { .. } => {
                body_kind = BodyKind::StaticInit;
                cx.lower_const_body(&mut module, def, const_ty, root);
            }
            // Defensive: a `BodyTy::Const` owner outside the known const-context DefKinds.
            _ => cx.unsupported.push(("body".to_string(), "non-fn body")),
        },
        // global-asm bodies routed through MIR for now.
        BodyTy::GlobalAsm(_) => cx.unsupported.push(("body".to_string(), "non-fn body")),
    }

    // Trust (C2-spans): transfer the per-body file interner so every stamped `SourceSpan.file`
    // resolves inside THIS mini-module. Crate assembly re-interns per spliced function.
    module.files = std::mem::take(&mut cx.files);

    Lowered {
        module,
        body_kind,
        unsupported: cx.unsupported,
        contains_call: cx.contains_call,
        place_path_carrier: cx.place_path_carrier,
        callees: cx.callees,
        pending_consts: cx.pending_consts,
        // Trust (totality Batch C): non-empty symbolic-const ledger ⇒ symbolic body.
        symbolic: !cx.symbolic_consts.is_empty(),
    }
}

/// Trust (wave-19): the `map_ty` FATNESS shape of a type, at the granularity that decides whether
/// two signatures link ABI-coherently. `sig_shapes_coherent` compares this per sig position between
/// a callee's IDENTITY-lowered record and a concrete instantiation, so a param that substitutes to a
/// fat DST (`&str`/`&[T]`) anywhere — top-level, behind a projection, or NESTED in an aggregate — is
/// caught. It is a PURE, side-effect-free mirror of `map_ty`'s fatness-relevant arms and MUST be kept
/// in lockstep with them (the same coupling `map_ty` has with the MIR-side oracle): if `map_ty`'s
/// ref/rawptr/aggregate fatness rules change, update this too or the gate silently drifts. Anything
/// `map_ty` cannot lower faithfully collapses to `Opaque` (the conservative catch-all).
#[derive(PartialEq, Eq)]
enum FatShape {
    /// A scalar (`bool`/`char`/int/uint/float) → `map_ty` gives a scalar `Ty`. A clean-identity
    /// scalar position is CONCRETE (a bare `ty::Param` is `Opaque`, never clean by value), so the
    /// identity and concrete scalar at one position are identical by construction — no need to
    /// distinguish widths.
    Scalar,
    /// A THIN pointer: `&T`/`&mut T` whose (normalized) pointee is not slice/str (incl. `&Self`,
    /// `&Param`, `&dyn`, `&mut [T]`), or a thin raw pointer → `map_ty` `Ty::Ptr`.
    Thin,
    /// A FAT shared slice/str reference `&[T]`/`&str` (`Mutability::Not`) → `map_ty` `Tuple([Ptr,I64])`.
    /// The pointee element is irrelevant to fatness (`&[U]` and `&[i32]` share the tuple shape).
    Fat,
    /// A tuple / concrete-length array / struct / enum, recursively — `map_ty` recurses into each
    /// element/field/variant, so the gate must too (a fat ref NESTED here flips fatness invisibly to
    /// a top-level-only check — the exact wave-19 adversarial finding).
    Agg(Vec<FatShape>),
    /// `map_ty` FAILS CLOSED (or would): a bare `ty::Param`/unresolved alias by value, a fat/array
    /// raw pointer, a const-generic-length array, a recursive/unsupported adt or enum, `dyn`, foreign,
    /// fn-ptr, closure, never, etc. An `Opaque` in the IDENTITY signature means the callee body itself
    /// failed closed at that position → it is DIRTY → a bodyless HAVOC declaration at assembly, so any
    /// instantiation links soundly and the position is SKIPPED (not a coherence constraint).
    Opaque,
}

/// Trust (wave-19): collapse an aggregate shape — if ANY component is `Opaque`, the whole aggregate
/// is `Opaque`. `map_ty` propagates a fail-closed component UP: a struct/tuple/array/fn-ptr with an
/// un-lowerable field/element (e.g. a by-value `ty::Param` field in `X<T>{a:T}` or a return `S<T>`)
/// pushes `unsupported` and dirties the WHOLE body → the callee is a HAVOC extern. `fat_shape` must
/// mirror that: without this, an identity `Agg([Opaque, Scalar,…])` is non-`Opaque` at the top, so
/// `sig_shapes_coherent` does NOT skip it and OVER-REJECTS a call whose callee is havoc anyway
/// (measured: 6 sized-arg calls like `S::<isize>::new::<f64>`/`bar(X<isize>)`). Collapsing preserves
/// the skip-`Opaque` invariant ("`Opaque` identity ⟺ havoc position") and hides NO real flip: a
/// genuine fat-flip vector is a ref-to-param (`&T`→`Thin`, non-`Opaque`), which never collapses, so
/// a struct-wrapped `Wrap<T>{r:&T}`→`Wrap<str>` flip is still `Agg([Thin,…])` vs `Agg([Fat,…])`.
fn agg_or_opaque(children: Vec<FatShape>) -> FatShape {
    if children.iter().any(|c| *c == FatShape::Opaque) {
        FatShape::Opaque
    } else {
        FatShape::Agg(children)
    }
}

/// Trust (wave-23, ref-escape memory model): true iff a [`FatShape`] is PURELY scalars and nested
/// scalar-aggregates — NO pointer/reference component (`Thin`/`Fat`/`Opaque`) anywhere, recursively.
/// A `&mut Struct` whose pointee has such a shape round-trips through a whole-aggregate `Load`/`Store`
/// with ZERO dropped metadata: there is no ref field whose `map_ty` fat-vs-thin collapse could make
/// the whole-struct read-modify-write ABI-unfaithful (the wave-19 DST-coherence hazard — a top-level
/// `Ty::Struct` gate would NOT catch a `&dyn`/`&mut [T]` field collapsed to thin `Ty::Ptr`, exactly
/// the drift that `fat_shape` recurses to expose). This conservatively excludes a struct with ANY ref
/// field (even a faithful thin `&T`); the precise "no fat-DST-collapsed field" relaxation (admitting
/// faithful thin / fat-shared-slice fields) is a documented follow-on, not needed for the seed corpus
/// (all `augmented-assignment::*_assign` receivers + scalar setters are pure-value structs).
fn is_pure_value_shape(s: &FatShape) -> bool {
    match s {
        FatShape::Scalar => true,
        FatShape::Agg(cs) => cs.iter().all(is_pure_value_shape),
        FatShape::Thin | FatShape::Fat | FatShape::Opaque => false,
    }
}

/// Trust (wave-OPTFLAG, 2026-07-09): Option-DISCRIMINANT lanes, ON BY DEFAULT (batteries
/// included — flags only disable powers). Set `TRUST_OPTION_FLAG_LANES=0` to disable; absent
/// or any other value keeps the lane ON.
///
/// Disabled (`TRUST_OPTION_FLAG_LANES=0`): behavior is BYTE-IDENTICAL to before this wave — a provably-opaque
/// `Option<T>` struct field (payload non-pure-value, e.g. `Option<RepaintKey>` /
/// `Option<Instant>`) collapses to a `Ty::Unit` lane in `struct_ty_rmw_opaque`, and a
/// variant store to it (`x.field = Some(v)` / `= None`) lowers as the opaque
/// extract/insert READ-BACK — the store is invisible in the IR, `Some` and `None`
/// indistinguishable.
///
/// Default (ON): that SAME lane registers as `Ty::Bool` — the Option's DISCRIMINANT — and a
/// LITERAL variant store lowers the discriminant as a real bool store (`= Some(..)` →
/// `const bool true`, `= None` → `const bool false`); the PAYLOAD expression is
/// deliberately not lowered (identical to the pre-wave opaque arm, which dropped the
/// whole RHS; bodies here are CLEAN-ONLY `NotRun`). This is what lets a temporal
/// extractor derive a present-liveness stamp/un-stamp protocol (aterm's
/// `WindowState::last_present: Option<RepaintKey>`) from the REAL statements.
///
/// A store whose RHS is not a literal `Some(..)`/`None` constructor (a copied Option
/// VALUE — unknown discriminant) commits `undef bool` — a sound HAVOC, NotRun-forced
/// (wave-RS; pre-wave it failed closed, which regressed real setter bodies flag-ON).
/// The READ side: wave-RS extends `read_opaque_option_lane` /
/// the Field-arm lane read to the `Ty::Bool` discriminant lane (is_some/is_none read
/// the REAL bool; `as_mut` carries the opaque payload while the discriminant stays
/// readable) — payload extraction beyond the opaque carrier still declines, and a
/// flag-OFF (`Ty::Unit`) lane keeps the pre-wave behavior byte-identically.
fn option_flag_lanes_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // Batteries included: ON BY DEFAULT (flags only disable powers). Absent — or any value
    // other than "0" — keeps the lane ON; ONLY the explicit `TRUST_OPTION_FLAG_LANES=0`
    // disables it.
    *ON.get_or_init(|| !std::env::var_os("TRUST_OPTION_FLAG_LANES").is_some_and(|v| v == "0"))
}

/// Trust (wave-RS, 2026-07-13): SHARED-borrow method-receiver PLACES, ON BY DEFAULT (batteries
/// included — flags only disable powers). Set `TRUST_SHARED_RECV_PLACE=0` to disable; absent
/// or any other value keeps the receiver places ON (the same channel convention as
/// `TRUST_OPTION_FLAG_LANES`).
///
/// Disabled (`TRUST_SHARED_RECV_PLACE=0`): behavior is BYTE-IDENTICAL to before this wave — a shared borrow
/// `&x.field` of a NON-scalar container lane in explicit-call-arg position lowers
/// through the general Borrow arms (typically the wave-25 interior shared-borrow
/// admission: the raw base pointer at field offset 0, or a byte-offset `gep`), which
/// carries NO field place — the measured eventlog-real gap: the real capacity test
/// `self.ring.len() > MAX_LOG_EVENTS` lowered but its receiver was unattributable, so
/// the capacity guard could not derive.
///
/// Default (ON): such a borrow lowers as the receiver's leaf-field VALUE instead — `Load`
/// the root struct + the `ExtractField` chain to the leaf (EXACTLY the wave-MC `&mut`
/// receiver place-path carrier, extended to `&`) — so a downstream temporal extractor
/// can attribute the callee (`len()` → an opaque scalar READ of the projected place).
///
/// SOUNDNESS: gated to NON-scalar leaves only (a scalar `&x.field` keeps its faithful
/// pointer/snapshot lowerings — its pointee bytes are semantically load-bearing); the
/// emitted call has `contains_call = true`, so the body is structurally NotRun
/// (CLEAN-ONLY — never interpreted/flipped/spliced), and the value-instead-of-pointer
/// receiver is only ever a PLACE-PATH carrier, the wave-MC argument verbatim. No write
/// can flow through a shared borrow, so no mutation is droppable through this carrier.
fn shared_recv_place_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // Batteries included: ON BY DEFAULT (flags only disable powers). Absent — or any value
    // other than "0" — keeps the receiver places ON; ONLY the explicit
    // `TRUST_SHARED_RECV_PLACE=0` disables it.
    *ON.get_or_init(|| !std::env::var_os("TRUST_SHARED_RECV_PLACE").is_some_and(|v| v == "0"))
}

struct LowerCx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    /// Trust (wave-DP): the identity of the body BEING LOWERED (`lower_module`'s `def`), for
    /// lanes gated on the current fn itself — today only the `Deref`/`DerefMut` ACCESSOR-body
    /// `&mut (*self).fieldK` interior-return lane (`try_lower_deref_accessor_interior_mut`),
    /// which must fire ONLY inside a `deref`/`deref_mut` impl method (anywhere else a `&mut`
    /// interior borrow keeps its fail-closed tag).
    body_def: DefId,
    next_value: u32,
    /// Block-id allocator. The entry block is always `BlockId::new(0)`; fresh blocks take 1, 2, …
    next_block: u32,
    /// SEALED blocks (already terminated), in creation order. The currently-open block is NOT here
    /// until `seal_with` moves it in.
    blocks: Vec<Block>,
    /// Body of the currently-open block.
    cur: Vec<InstrNode>,
    /// Id of the currently-open block.
    cur_id: BlockId,
    /// Trust (C2-spans): span of the THIR expr currently being lowered — stamped onto every
    /// instruction by `push_node`, set/restored by the `lower_expr` wrapper so each instruction
    /// is attributed to the INNERMOST expr that emitted it.
    cur_span: Option<SourceSpan>,
    /// Trust (C2-spans): per-body file interner mirroring `Module::intern_file` (dedup by
    /// position). Transferred into the mini-module at finalize; the crate-assembly splice
    /// re-interns per function so `SourceSpan.file` never dangles.
    files: Vec<String>,
    /// Trust (C2-names): `(ValueId, source name)` ledger, stamped onto the Function at
    /// `finish_body` (binary v32 `value_names`). Params only for now — ValueId(i) IS entry
    /// param i by construction, so the ledger cannot desync from the signature.
    value_names: Vec<(ValueId, String)>,
    /// Params of the currently-open block (entry params seeded in `lower_fn`; join blocks get a
    /// single result param via `start_block`).
    cur_params: Vec<(ValueId, Ty)>,
    /// True iff the open block has already been terminated (by `Return`, or an `if` whose arms both
    /// diverged). When set, callers must not append instructions or emit a fall-through branch.
    sealed: bool,
    /// Binding environment: source `LocalVarId` → current `ValueId` (last-write-wins for shadowing).
    locals: Vec<(LocalVarId, ValueId)>,
    /// Trust: source `LocalVarId` → its declared (interpretable) `trust_ir::Ty`, recorded once at the
    /// local's first bind. A Rust local's type is invariant across reassignments, so this is the type
    /// the merge machinery gives a local's join block-param when it is mutated inside an `if`/`match`.
    local_tys: Vec<(LocalVarId, Ty)>,
    /// Set when an `Inst::Call` / `Inst::CallIndirect` is emitted (see `Lowered::contains_call`).
    contains_call: bool,
    /// Trust (B3-2c seam guard): see the public flag — set by the receiver
    /// place-path carrier lanes.
    place_path_carrier: bool,
    /// Trust: callee identity ledger (see `Lowered::callees`) — appended by
    /// `admit_callee` (via `resolve_callee` / `resolve_reify_target`), deduplicated on full
    /// identity so a callee invoked twice records once but a genuine index collision (two
    /// identities, one `FuncId`) keeps both entries and is detected as ambiguous at
    /// crate-level assembly.
    callees: Vec<CalleeRef>,
    /// Trust: LOCAL consts deferred to the crate finalizer (see `Lowered::pending_consts` /
    /// [`PendingConst`]) — appended by `lower_named_const`'s reentrancy-safe deferral path,
    /// one entry per emitted placeholder `Inst::Const`.
    pending_consts: Vec<PendingConst>,
    /// Trust: fn-pointer signature `FuncTy`s minted during the body walk (`pend_func_ty`),
    /// flushed into the per-body `Module` at the end of `lower_fn`. Table-id convention:
    /// slot 0 is ALWAYS the function's own signature (interned by `lower_fn` before the walk),
    /// so a pended entry at position `i` is `FuncTyId(1 + i)` — the id `Ty::Func` /
    /// `Inst::CallIndirect { sig }` embed. The flush appends in pend order, and a tripwire
    /// fails the body closed if anything else grew the table in between (checked, not assumed).
    pending_func_tys: Vec<FuncTy>,
    /// Trust (B6, RFC TRUST_IR_V2 — v25 Fn/ByValue slice): first-class `ClosureTy` entries
    /// minted during the body walk (`pend_closure_ty`) for by-value FnOnce closure envs.
    /// Table-id convention: the per-body module's `closure_types` table starts EMPTY, so a
    /// pended entry at position `i` is `ClosureTyId(i)`; the flush appends in pend order with
    /// a desync tripwire, exactly like `pending_tys`.
    pending_closure_tys: Vec<trust_ir::ClosureTy>,
    /// Trust: module-`types`-table entries minted during the body walk (`pend_ty`) — today only
    /// the element type of a ZERO-LENGTH array `[T; 0]`, whose `map_ty` spelling is
    /// `Ty::Array(TyId, 0)` (the MIR-side oracle's exact convention — `map_type_ctx` interns the
    /// elem via `add_type`; the `Ty::Tuple([])` spelling was a guaranteed signature-divergence
    /// class). Table-id convention: the per-body module's `types` table starts EMPTY (nothing
    /// else adds to it), so a pended entry at position `i` is `TyId(i)`. The flush appends in
    /// pend order with a desync tripwire, exactly like `pending_func_tys`.
    pending_tys: Vec<Ty>,
    /// Trust (wave-16): promoted-borrow module GLOBALS minted during the body walk (the
    /// `Borrow(non-local place)` → `Inst::GlobalAddr` lowering of a rustc-PROMOTED shared
    /// borrow of a scalar const-expr — `fn f()->&'static i32 { &5 }`, `&C`, `&123u8`,
    /// `&true`, `&1.5f32`), flushed into the per-body `Module.globals` at the end of the body
    /// in `finish_body`. Table-id convention: the per-body module's `globals` table starts
    /// EMPTY (nothing else adds to it), so a pended entry at position `i` is `GlobalId(i)` —
    /// the id the emitted `Inst::GlobalAddr { global }` embeds. The flush appends in pend order
    /// with a desync tripwire, exactly like `pending_tys`. The crate assembler (`crate_module`)
    /// re-interns these into the assembled module (append + crate-unique names) and remaps every
    /// embedded `GlobalId`; each is CHECKED spliceable (scalar `ty` + scalar `Constant`
    /// initializer) in `splice_ok`, never assumed.
    pending_globals: Vec<Global>,
    /// Trust (B2-3): trait-object id COLLISION TRIPWIRE. `FatPtrKind::TraitObject`'s
    /// `trait_id` is the CONTENT hash of the principal trait's def path
    /// (`trust_ir::stable_trait_object_id` — the ONE shared mint, also used by the
    /// oracle bridge), so splicing may clone the kind verbatim with no remap table.
    /// The one failure mode that discipline cannot catch is a 32-bit hash collision
    /// across DISTINCT def paths — `trait_object_id` records every (id, path) it
    /// issues and refuses the mint on a collision (the caller fail-closes the body
    /// with a coverage tag; a wrong-but-plausible id must never be emitted).
    trait_object_ids: Vec<(u32, String)>,
    /// Trust (totality Batch C): SYMBOLIC assoc-const ledger — one entry per distinct
    /// `(const DefId, args)` this body reads whose args carry a live generic param
    /// (`B::BOOL`, `U::USIZE`, …). Each entry owns one body-scoped EXTERN IMMUTABLE
    /// global (`initializer: None`, `Linkage::External` — trust-ir's "declared, value
    /// unknown" vocabulary); every read of the same pair emits `GlobalAddr` + `Load`
    /// against the SAME id, so read-read equality is preserved by the one-immutable-
    /// global structure. Non-empty ⇒ the body is SYMBOLIC: it lowers (coverage) but is
    /// excluded from the interpretation differential (a value-less load would
    /// manufacture a false TypeError-vs-value verdict) and from the crate-module
    /// splice (the assembled executable module must not contain value-less globals) —
    /// both gates CHECKED at their seams, never inferred (`Lowered::symbolic`).
    symbolic_consts: Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>, GlobalId)>,
    /// Trust (wave-SR2): one emitted global per `static` DefId read by this body, so every read
    /// of the same static resolves to the SAME `GlobalId` (read-read equality is structural).
    static_globals: Vec<(rustc_span::def_id::DefId, GlobalId)>,
    unsupported: Vec<(String, &'static str)>,
    /// Trust (v2 Phase 0b): COLLECT-ALL measurement mode — failure seams that normally
    /// short-circuit sibling subtrees (first bad call arg, …) record their tag and keep walking,
    /// so `unsupported` approaches the body's full leaf demand. The lowered output under this
    /// flag is measurement-only garbage (see `lower_module_collect_all`); the flag must gate
    /// ONLY extra `continue` paths, never change what the strict pass emits.
    collect_all: bool,
    /// Trust: struct registration ledger. Each Rust struct `AdtDef` is registered ONCE as a
    /// `trust_ir::StructDef` (dedup by its `DefId` → assigned `StructId`); `pending_structs` holds
    /// the defs to flush into the `Module` in `lower_fn` (where `&mut Module` is in scope). The
    /// runtime *value* shape is first-class `Ty::Struct(id)` (the pinned interpreter materializes
    /// `(Ty::Struct, Constant::Aggregate)` seeds — foundations commit 93e8f16); nested field
    /// registration is depth-first, so a field's `Ty::Struct(inner)` always has `inner < parent`
    /// in this ledger (the splice's remap-order invariant; checked there, not assumed).
    // Trust (B3-4 T1): keyed by (DefId, GenericArgsRef) — NOT DefId alone. Two
    // instantiations of one generic struct in one body (Pair<i32> + Pair<bool>)
    // have DISTINCT field types; a DefId-only key silently discards the second
    // instantiation's field_tys and signs a wrong-shape def (the enum ledger
    // fixed this exact bug first — mirror of `enum_ids`).
    /// Trust (totality Batch B): keyed by `(DefId, GenericArgsRef)` — a generic struct's
    /// distinct instantiations have DISTINCT field types after substitution and must get
    /// distinct `StructDef`s (the DefId-keyed ledger aliased `Wrapper<u8>` and
    /// `Wrapper<u32>` to whichever registered first — a confirmed latent field-type bug).
    struct_ids: Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>, trust_ir::StructId)>,
    pending_structs: Vec<trust_ir::StructDef>,
    /// Trust: enum registration ledger — the enum counterpart of `struct_ids`/`pending_structs`
    /// and the sole first-class `Ty::Enum(id)` path. Dedup is by
    /// `(DefId, GenericArgs)` — NOT `DefId` alone — because two instantiations of one generic
    /// enum (`E<i32>` vs `E<bool>`) have DIFFERENT variant field types and must not share an
    /// `EnumDef`. Registration (`register_enum`) admits ONLY variants whose every field is a
    /// seedable scalar (`seed_constant`: ints/bool/floats), the exact set the pinned
    /// interpreter's `enum_layout` provably sizes — a clean body must never carry an enum whose
    /// first construction traps `enum_layout` (that would be a manufactured differential
    /// divergence, scratch-verified cmtest w5_enum). Consequently a registered `EnumDef`'s
    /// variant fields are always TABLE-FREE — the splice invariant `crate_module::splice_ok`
    /// CHECKS (never assumes) before interning enum defs FIRST (structs may reference enums,
    /// never vice versa). Ids are positional (`pending_enums[i].id == i`), matching
    /// `Module::add_enum`'s verbatim push at the `lower_fn` flush.
    enum_ids: Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>, trust_ir::EnumId)>,
    /// Trust: enums `register_enum` DECLINED, cached so a nested-enum tower short-circuits
    /// instead of re-walking every level per enclosing variant (V^depth blowup; see the
    /// negative-cache comment in `register_enum`).
    enum_declined: Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    pending_enums: Vec<trust_ir::EnumDef>,
    /// Trust: Adt INSTANTIATIONS currently being field-mapped, innermost last — the cycle
    /// guard for `struct_field_tys`/`register_enum` ↔ `map_ty` mutual recursion on RECURSIVE
    /// types (`struct S(fn(S))`, `struct T { next: *const T }`): re-entering an Adt already on
    /// the stack fails closed instead of overflowing the stack (wave-2 found the SIGBUS).
    ///
    /// Trust (totality Batch B): keyed by `(DefId, GenericArgsRef)`, NOT bare DefId — a
    /// DefId-keyed guard false-positives on the NESTED-INSTANTIATION shape (`UInt<UInt<..>>`,
    /// typenum's whole vocabulary): walking `UInt<U1, B0>`'s field of type `UInt<U0, B1>`
    /// re-enters the same DefId at DIFFERENT args, which is a finite DAG walk, not a cycle.
    /// A genuine cycle re-enters the same (DefId, args) PAIR and still fails closed. Keying
    /// alone does not terminate (polymorphic recursion behind pointers admits unboundedly
    /// many distinct pairs), so [`ADT_VISIT_FUEL`] bounds the DEPTH — see its doc.
    adt_visit_stack: Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    /// Trust: enclosing-loop stack, innermost last. Each `ExprKind::Loop` pushes a `LoopCtx` (its
    /// header/exit block ids + the loop-carried local set) before lowering its body and pops it after.
    /// `Break`/`Continue` resolve to the innermost entry; the loop's `region::Scope` label is recorded
    /// so a labeled `break 'l`/`continue 'l` that does NOT target the innermost loop fails closed
    /// (we do not model multi-level breakout yet). Non-empty ⇒ a loop already in flight, so a NESTED
    /// `Loop` fails closed (single-loop scope for now — see `lower_loop`).
    loop_stack: Vec<LoopCtx>,
    /// Trust: `ValueId`s that hold a borrow-produced `Ty::Ptr` (from the `ExprKind::Borrow` arm),
    /// plus (wave-5) REF-TYPED scalar-pointee PARAMS registered at binding time in `lower_fn` —
    /// a `&T`/`&mut T` param is the CALLER's slot pointer, consumed by exactly the same
    /// `Deref`→`Load` machinery. The memory foothold supports the `let r = &x; …; *r` pattern
    /// (and the param equivalent `fn f(r: &T) { … *r }`): the `Ty::Ptr` flows into a `Deref`
    /// (`Load`), a `*r = v` write (`Store`, mut ledger only), a reborrow (`&*r` / call-arg
    /// forwarding), or a call argument (see `lower_call_args` for the faithfulness proof). Any
    /// OTHER consumption — returning it, storing it into another local (`set_local`), putting it
    /// in a tuple/struct field, or feeding it to a binary op — would need real aliasing/escape
    /// modeling we do not have. Each value-consuming site checks `is_borrow_ptr` and fails
    /// closed if a borrow pointer would escape.
    borrow_ptrs: Vec<ValueId>,
    /// Trust (wave-14): the SUBSET of `borrow_ptrs` that originate from a REFERENCE PARAMETER
    /// (registered at param binding, `ValueId::new(param_index)`) — NOT the `&x`/`&s.field`/`&arr[i]`
    /// snapshot borrow-ptrs (those are `fresh()` ids `>= params.len()`, so the two are disjoint by
    /// construction: `next_value` starts at `params.len()`). A ref param's pointer is caller-provided
    /// and provably OUTLIVES the call, so RETURNING it (`fn f(x:&T)->&T{x}`, or `&*x` which forwards
    /// to the same param ptr) is faithful — the trust-ir `Return` yields the very pointer the source
    /// returns, no snapshot, no synthesis, and borrowck has already proven the lifetime. This is what
    /// lets the return-escape guards ADMIT a returned ref param while keeping every other borrow-ptr
    /// (a `&local` snapshot, whose referent dies at return — borrowck-rejected anyway) fail-closed.
    ref_param_ptrs: Vec<ValueId>,
    /// Trust (wave-16): the SUBSET of `borrow_ptrs` that hold a promoted-borrow `Inst::GlobalAddr`
    /// pointer (`&5` / `&C` / `&<scalar const-expr>` lowered to a module GLOBAL's address). A
    /// GlobalAddr pointer is `'static` (the global outlives every call), so RETURNING it
    /// (`fn f()->&'static i32 { &5 }`) is faithful — the trust-ir `Return` yields the very address
    /// the source returns. This mirrors `ref_param_ptrs`: the pointer is ALSO in `borrow_ptrs`, so
    /// every OTHER escape guard (binary operand / tuple/struct/array field / `*r =` write / cast /
    /// call in a value position needing modeling) still fails closed on it; only the two
    /// return-escape guards make an exception for `global_ptrs` (as they do for `ref_param_ptrs`).
    /// Disjoint from `ref_param_ptrs` (a global address is not a caller pointer) and from
    /// `mut_borrow_ptrs` (the global is immutable).
    global_ptrs: Vec<ValueId>,
    /// Trust (wave-25b): the SUBSET of `borrow_ptrs` that are DERIVED INTERIOR pointers — a flat-I8
    /// `GEP` of a ref-PARAM pointer to a struct field at a non-zero byte offset (`&self.field`,
    /// `offset != 0`; the offset-0 case returns the raw param ptr verbatim and needs no ledger). Like
    /// `ref_param_ptrs`, the pointee is CALLER memory that provably outlives the call, so RETURNING it
    /// (`fn get(&self) -> &T { &self.field }`) is faithful — the trust-ir `Return` yields the very
    /// interior address. It earns its OWN ledger rather than reusing `ref_param_ptrs` (whose members
    /// are the raw param ptrs at `ValueId::new(param_index)`, NOT `fresh()` derived ids — see its doc)
    /// or `global_ptrs` (whose members are `'static` globals, NOT caller pointers). The pointer is
    /// ALSO in `borrow_ptrs`, so every OTHER escape guard fails closed on it; only the two
    /// return-escape guards make an exception for `interior_ptrs` (as they do for the other two).
    /// The byte offset is sourced ONLY from rustc's authoritative `layout.fields.offset` (never
    /// hand-computed): the interior-borrow-return wave is clean-only / `NotRun` / never-flipped, so a
    /// wrong offset would be invisible to the interpreter and the flip burn-in — faithfulness holds by
    /// construction, gated further by requiring the borrow's own result type to map to a thin
    /// `Ty::Ptr` (a fat/DST field-ref is fail-closed).
    interior_ptrs: Vec<ValueId>,
    /// Trust: locals that are `&mut`-borrowed SOMEWHERE in the function (the pre-pass result). Such a
    /// local cannot stay SSA — a write through the pointer (`*r = v`) must be visible to later reads —
    /// so it is PROMOTED to a single memory slot for its whole lifetime: an `Alloca` at its `let`/param,
    /// reads `Load` from the slot, writes (`local = v`) `Store` to it, `&mut local` yields the slot Ptr,
    /// and `*r = v` `Store`s through that Ptr. A promoted local is NEVER `set_local`'d, so it never
    /// appears in `locals` and is therefore automatically excluded from every SSA block-param merge
    /// (`if`/`match`/loop) — the memory model is its single source of truth.
    promoted: Vec<LocalVarId>,
    /// Trust: promoted local → its `Alloca` slot `ValueId` (a `Ty::Ptr`), recorded once when the local's
    /// `let`/param emits the slot. Reads/writes/`&mut` of the local resolve their slot here.
    promoted_slots: Vec<(LocalVarId, ValueId)>,
    /// Trust: promoted local → its (interpretable scalar) pointee `Ty`, recorded with the slot so a
    /// `Load`/`Store` against the slot carries the right element type.
    promoted_tys: Vec<(LocalVarId, Ty)>,
    /// Trust: `ValueId`s that hold a `&mut`-produced slot pointer (the `ExprKind::Borrow{Mut}` arm
    /// yields the promoted local's slot Ptr here; wave-5 adds `&mut T` scalar-pointee PARAMS —
    /// the caller's slot pointer — at binding time). Distinct from `borrow_ptrs` (shared) so the
    /// `*r = v` write arm (`ExprKind::Assign` with a `Deref` lhs) can recognize a writable target.
    /// Each such Ptr is ALSO pushed into `borrow_ptrs` so all the existing escape guards (return /
    /// call-arg / tuple/struct field / binary operand) fail closed on it too — the only legitimate
    /// consumers are a `Deref` read (`Load`) and a `*r = v` write (`Store`).
    mut_borrow_ptrs: Vec<ValueId>,
    /// Trust (wave-ER): locals bound as OPAQUE CARRIERS by this wave's channels —
    /// (a) a `let`-pattern payload binding over an OPAQUE (non-pure) enum scrutinee
    /// (`ExprKind::Let` in a let-chain / let-`else`: `if let Some(sb) = …as_mut()` — the
    /// payload of an opaque enum value is itself opaque), bound to the scrutinee's own SSA
    /// value at `Ty::Unit`; (b) a `&mut`-borrowed NON-pure aggregate local that even the
    /// registered-opaque channel (`opaque_local_aggregate_ty`) could not type — a std
    /// container root like the erase ring-rebuild's `new_rows: Vec<Row>` — bound to its init
    /// value at `Ty::Unit`. The ONLY pointer-flavored consumer admitted for such a local is
    /// the method-receiver VALUE carrier (`try_lower_receiver_place_value`, the wave-MC
    /// opaque-call posture: `contains_call` ⇒ NotRun, so the receiver need not be a real
    /// pointer); every other pointer use fails closed at its own site. The for-loop summary
    /// gate (`foreach_summary_scan`) deliberately REFUSES writes through `*<opaque carrier>`
    /// (a write into an opaque LANE's payload is not an "unprojected local rebuild" — see
    /// the drain transfer-loop note there).
    opaque_carrier_locals: Vec<LocalVarId>,
    /// Trust (wave-SEAM, 2026-07-13): OPTION-DISCRIMINANT VALUE-LANE ledger, gated by
    /// `TRUST_OPTION_FLAG_LANES` (ON BY DEFAULT; set `=0` to disable — the same channel as the field lanes). Under the
    /// flag, an OPAQUE-LANE `Option<T>` (both enum type models decline — `is_opaque_lane_enum`)
    /// carries its DISCRIMINANT as a `Ty::Bool` VALUE (see `map_ty`'s enum arm): a literal
    /// `None`/`Some(..)` constructor in VALUE position lowers to `const bool` (payload
    /// deliberately dropped — the field write side's CLEAN-ONLY posture; `contains_call`
    /// forced), and a DIRECT call to a LOCAL fn whose result type is such an Option yields the
    /// callee's mapped `Ty::Bool` return. This ledger records exactly the values PROVEN to be
    /// such discriminants (ctor consts, local-callee results, and an if/else JOIN param whose
    /// every reaching arm value is itself ledgered) — the `if let Some(x) = <local>` value-lane
    /// test (`lower_let_opaque_test`) admits ONLY a scrutinee whose bound value is ledgered, so
    /// a surrogate-typed extern-call result or an unproven merge can never silently become a
    /// REAL branch condition (fail-closed: such scrutinees keep the pre-wave paths verbatim).
    option_lane_values: Vec<ValueId>,
    /// Trust: the function's declared RETURN type (the sig output), recorded at `lower_fn` entry. The
    /// `?`-operator lowering (`lower_try_question`) needs it to synthesize the early-return enum value
    /// (`Err(e)` / `None`) the `Try::from_residual(residual)` desugar produces — `from_residual` is a
    /// trait method the producer cannot resolve, so for the IDENTITY case (the operand's error/None
    /// type matches the fn's, no `From`-conversion) we build the return enum directly from the operand
    /// payload instead. `None` until `lower_fn` runs (defensive).
    fn_return_rty: Option<RustcTy<'tcx>>,
}

/// Trust (wave-ER): accumulator for `foreach_summary_scan` (the read-only-escape `for`-loop
/// summary gate): locals the region can MUTATE (assign/`&mut` targets), locals DECLARED by
/// patterns inside the region, `Scope` ids seen, and `break`/`continue` labels (which must all
/// target scopes inside the region).
#[derive(Default)]
struct ForSummaryScan {
    mutated: Vec<LocalVarId>,
    declared: Vec<LocalVarId>,
    scopes: Vec<region::Scope>,
    jumps: Vec<region::Scope>,
}

/// Trust: what the THIR reborrow peel bottomed out at (see `reborrow_target`).
enum ReborrowTarget {
    /// A bare LOCAL place (possibly through `&*(&x)` layers) — route to the existing
    /// snapshot-alloca / promoted-slot admissions.
    Local(LocalVarId),
    /// `Deref{ e }` of a NON-borrow, `ty::Ref`-typed expr (a ref binding): the place's address
    /// IS `e`'s value — lower it and require a known borrow pointer.
    Ptr(ExprId),
    /// A genuinely non-local place (`&a.b`, `&a[i]`, through a raw pointer) — fail closed.
    NotAPlace,
}

/// Trust: how a THIR call's function operand resolved (see `resolve_callee`).
enum CalleeKind {
    /// Statically-known callee: emit `Inst::Call { callee }` (DefIndex-derived, ledgered).
    Direct(FuncId),
    /// A first-class fn-pointer VALUE operand (the peeled callee `ExprId`, of `ty::FnPtr`
    /// type): lower it to a value and emit `Inst::CallIndirect` with its mapped signature.
    FnPtr(ExprId),
    /// Trust: `Fn`/`FnMut::call{,_mut}` on a NON-CAPTURING local closure, resolved to the
    /// closure body itself (`InstanceKind::Item` — see `resolve_fn_trait_callee`). The call
    /// site must UNTUPLE the rust-call args honestly: the THIR shape is
    /// `[receiver, (tupled-args)]` while the closure body's real (wave-1-signed) convention is
    /// `(env: Ptr, declared…)`, so the emitted `Inst::Call` carries
    /// `[fresh unit-slot env Ptr, untupled elements…]` (see the `ExprKind::Call` arm).
    /// `callee` is the closure body's DefIndex-derived, ledgered `FuncId` (`admit_callee`),
    /// spliced at crate-level assembly exactly like any other local body.
    ///
    /// Trust (wave-CF): `capturing` distinguishes a CAPTURING Fn/FnMut closure (`|| x+1`, a
    /// non-empty `upvar_tys`) from the wave-5 non-capturing case. When `capturing`, the call site
    /// materializes the REAL env (a `Ty::Tuple(captures)` value built by the `ExprKind::Closure`
    /// value arm and bound to the closure local) into a fresh slot and passes its address — the
    /// closure BODY (wave-CE) `Load`s `Ty::Tuple(captures)` through it. When NOT `capturing`, the
    /// env is the wave-5 fresh unit-slot Ptr (zero captures → no upvar projection can exist).
    ClosureCall { callee: FuncId, capturing: bool },
}

/// Trust: one enclosing-loop frame for `Break`/`Continue` resolution.
struct LoopCtx {
    /// The loop's `region::Scope` (the label a `break`/`continue` carries). An unlabeled
    /// `break`/`continue` inside this loop carries exactly this scope, so an equality check both
    /// (a) confirms the target is THIS loop and (b) rejects a `break 'outer` aimed elsewhere.
    scope: region::Scope,
    /// Loop-header block (the back-edge / `continue` target). Carries one block-param per carried local.
    header: BlockId,
    /// Loop-exit block (the `break` target). Successor reached when the loop terminates.
    exit: BlockId,
    /// The loop-carried locals (a local assigned somewhere in the body), in stable order, with the
    /// header block-param `ValueId` each is bound to on header entry. Back-edge/`continue` `Br`s pass
    /// these locals' CURRENT values as args; the `exit` reads them at their header-param versions.
    carried: Vec<(LocalVarId, ValueId, Ty)>,
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    fn fresh(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    /// Allocate a fresh, never-before-used `BlockId`.
    fn fresh_block_id(&mut self) -> BlockId {
        let b = BlockId::new(self.next_block);
        self.next_block += 1;
        b
    }

    /// Begin building a new open block `id` with the given params. Callers normally `seal_with` the
    /// previous block first; this just resets the cursor (and clears `sealed`).
    fn start_block(&mut self, id: BlockId, params: Vec<(ValueId, Ty)>) {
        self.cur_id = id;
        self.cur_params = params;
        self.cur = Vec::new();
        self.sealed = false;
    }

    /// Seal the currently-open block by appending `terminator` (which MUST be a terminator `Inst`)
    /// and moving the finished `Block` into `self.blocks`. The caller is expected to `start_block`
    /// next if there is a successor.
    fn seal_with(&mut self, terminator: Inst) {
        assert!(!self.sealed, "seal_with cannot seal the same block twice");
        assert!(terminator.is_terminator(), "seal_with requires a terminator");
        self.push_node(InstrNode::new(terminator));
        let mut block = Block::new(self.cur_id);
        for (v, ty) in std::mem::take(&mut self.cur_params) {
            block = block.with_param(v, ty);
        }
        block.body = std::mem::take(&mut self.cur);
        self.blocks.push(block);
        self.sealed = true;
    }

    /// Minimal `rustc ty -> trust_ir::Ty`. Fail-closed: unmapped types are recorded.
    /// Trust (B2-3): mint the trait-object id for a principal trait def — the ONE
    /// shared convention (`trust_ir::stable_trait_object_id` over the UNTRIMMED def
    /// path string, the exact string the oracle's `safe_def_path_str` renders from
    /// the same `DefId`), with a per-body COLLISION TRIPWIRE: two distinct def paths
    /// hashing to one id refuse the mint (`None`; the caller fail-closes with a
    /// coverage tag). A wrong-but-plausible id is the one failure mode the verbatim
    /// splice clone cannot catch — `remap_ty` copies the kind BECAUSE ids are
    /// content-stable, never positional.
    fn trait_object_id(&mut self, principal: rustc_span::def_id::DefId) -> Option<u32> {
        // Trust (B3-4 gate catch, 2026-07-20): the SPELLING must match the oracle's
        // `safe_def_path_str` wrapper stack EXACTLY (no_trimmed + no_visible +
        // resolve_crate_name) — the mint is shared but a re-exported principal
        // (std::fmt::Debug vs core::fmt::Debug) hashes differently under
        // different path-rendering modes, and the differential caught exactly
        // that as trait_id sig-divergences when the oracle side gained the
        // no_visible/resolve wrappers.
        let path = rustc_middle::ty::print::with_resolve_crate_name!(
            rustc_middle::ty::print::with_no_visible_paths!(
                rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(principal))
            )
        );
        let id = trust_ir::stable_trait_object_id(&path);
        match self.trait_object_ids.iter().find(|(existing_id, _)| *existing_id == id) {
            Some((_, existing_path)) if *existing_path != path => None,
            Some(_) => Some(id),
            None => {
                self.trait_object_ids.push((id, path));
                Some(id)
            }
        }
    }

    fn map_ty(&mut self, ty: RustcTy<'tcx>) -> Ty {
        match ty.kind() {
            ty::Bool => Ty::Bool,
            // Trust (totality Batch A): the never type `!` is first-class in trust-ir
            // (`Ty::Never`; the bridge maps it 1:1, trust-ir-bridge lower.rs:177). A
            // `!`-typed VALUE is unreachable by construction, so mapping the type is
            // trivially faithful; this retires the catch-all "Ty" tag on `-> !`
            // signatures and diverging call expressions. Value-position uses that
            // would need materialization still fail closed at their own gates
            // (`is_scalar_ty(Never)` is false).
            ty::Never => Ty::Never,
            ty::Int(ty::IntTy::I8) => Ty::I8,
            ty::Int(ty::IntTy::I16) => Ty::I16,
            ty::Int(ty::IntTy::I32) => Ty::I32,
            ty::Int(ty::IntTy::I64) => Ty::I64,
            ty::Int(ty::IntTy::I128) => Ty::I128,
            ty::Uint(ty::UintTy::U8) => Ty::U8,
            ty::Uint(ty::UintTy::U16) => Ty::U16,
            ty::Uint(ty::UintTy::U32) => Ty::U32,
            ty::Uint(ty::UintTy::U64) => Ty::U64,
            ty::Uint(ty::UintTy::U128) => Ty::U128,
            // Trust (v25 B1): pointer-width ints carried FAITHFULLY as trust-ir's
            // first-class `Ty::Isize`/`Ty::Usize` — the historical fixed-width
            // I64/U64 respell (which destroyed isize-ness and forced the shim's
            // PtrSpell inversion + ledger row L12) is RETIRED. Width resolves at
            // the CONSUMER via `bit_width_with(pointer_bits)`; the pinned
            // interpreter and every downstream gate execute them at the 64-bit
            // reference width. The MIR-side oracle keeps the identity through
            // `extract_function_faithful` (TrustTy::PtrSizedInt), so differential
            // signatures agree by leaf equality. Non-64-bit targets stay
            // fail-closed until multi-target validation exists (same honesty as
            // the old exotic-width arms).
            ty::Int(ty::IntTy::Isize) => match self.tcx.data_layout.pointer_size().bits() {
                64 => Ty::Isize,
                bits => {
                    self.unsupported.push((format!("isize@{bits}bits"), "Ty(isize-width)"));
                    Ty::Unit
                }
            },
            ty::Uint(ty::UintTy::Usize) => match self.tcx.data_layout.pointer_size().bits() {
                64 => Ty::Usize,
                bits => {
                    self.unsupported.push((format!("usize@{bits}bits"), "Ty(usize-width)"));
                    Ty::Unit
                }
            },
            // Trust: floats. `f32`/`f64` → `Ty::F32`/`Ty::F64` — byte-for-byte the MIR-side
            // oracle's convention (trust-ir-bridge lower.rs:164-165 maps `Ty::Float{32/64}` to
            // `TrustIrTy::F32/F64`), so differential signatures agree. Float VALUES are IEEE-754
            // bit patterns end-to-end: literals are `Constant::Float` (the interpreter converts
            // via `float_bits_from_f64`, exact for every f32 because f64 superset-represents f32),
            // arithmetic is the trap-free `FAdd/FSub/FMul/FDiv/FRem` family (floats do NOT trap —
            // MIR gates every overflow/div-zero assert on `ty.is_integral()`,
            // as_rvalue.rs:449/473/522), and comparisons are `Inst::FCmp` with the oracle's exact
            // ordered/unordered table. `f16`/`f128` stay FAIL-CLOSED (precise tag): the pinned
            // interpreter refuses f16 constants/arithmetic ("requires an explicit half-precision
            // codec") and the MIR-side extraction refuses both widths' constants.
            ty::Float(ty::FloatTy::F32) => Ty::F32,
            ty::Float(ty::FloatTy::F64) => Ty::F64,
            ty::Float(ty::FloatTy::F16 | ty::FloatTy::F128) => {
                self.unsupported.push((format!("{ty:?}"), "Ty(float-width)"));
                Ty::Unit
            }
            // Trust (v25 B1): `char` carried FAITHFULLY as trust-ir's first-class
            // `Ty::Char` — a 32-bit carrier whose Unicode-scalar valid range is
            // the validator's checked claim. Operations still act on the code-
            // point bits (Switch dispatch, unsigned ICmp, casts through the
            // 32-bit paths); the wave-T `Ty::U32` respell and its flip-side
            // `abi_char_u32_pair` carve-out are RETIRED. The oracle keeps char
            // identity via `extract_function_faithful` (TrustTy::Char), so
            // differential signatures agree by leaf equality.
            ty::Char => Ty::Char,
            // Trust: tuples → `Ty::Tuple` of the (recursively mapped) element types. The empty
            // tuple `()` is the unit type — keep it as `Ty::Unit` so a `()`-returning body stays on
            // the existing 0-value path (the interpreter cannot materialize a `Ty::Tuple([])`). Any
            // element type that is itself unsupported pushes its own `unsupported` entry via the
            // recursive `map_ty`, keeping the gate fail-closed.
            ty::Tuple(elems) if elems.is_empty() => Ty::Unit,
            ty::Tuple(elems) => {
                let mapped: Vec<Ty> = elems.iter().map(|e| self.map_ty(e)).collect();
                Ty::Tuple(mapped)
            }
            // Trust: a struct `ty::Adt` → FIRST-CLASS `Ty::Struct(id)` over a `trust_ir::StructDef`
            // registered ONCE (dedup by `DefId`; ids positional, nested fields depth-first so
            // inner < outer). This is byte-for-byte the MIR-side oracle's convention
            // (trust-ir-bridge `map_type_ctx` maps `Ty::Adt → TrustIrTy::Struct(struct_id)`), so
            // the differential compares the two sides' STRUCTURALLY-RESOLVED shapes (each module
            // numbers its own ids; see `differential::tys_agree`). The pinned trust-ir interpreter
            // (foundations commit 93e8f16, on pin da92c54) materializes a `Const`-seeded
            // `(Ty::Struct, Constant::Aggregate)` — scratch-verified (cmtest w4_struct) — so
            // construction/projection reuse the exact tuple `InsertField`/`ExtractField` machinery
            // under the struct type. Enums/unions fall through to fail-closed `unsupported`. A
            // field type that is itself unsupported records its own `unsupported` entry via the
            // recursive `map_ty`.
            ty::Adt(adt, args) if adt.is_struct() => match self.struct_field_tys(*adt, *args) {
                Some(field_tys) => Ty::Struct(self.register_struct(*adt, *args, &field_tys)),
                None => {
                    self.unsupported.push((format!("{ty:?}"), "Ty(struct-fields)"));
                    Ty::Unit
                }
            },
            // Trust (B3-2c): every admitted enum maps to `Ty::Enum(registered EnumId)`
            // over a `trust_ir::EnumDef`
            // carrying the variants' names/field types + EXPLICIT rustc discriminants + the
            // `#[repr(iN)]` hint. The pinned interpreter (foundations 5e6cb93, on pin da92c54)
            // materializes `(Ty::Enum, Constant::Aggregate([Int(disc), fields...]))` seeds, reads
            // the tag positionally as field 0 (typed as the EnumDef's CANONICAL tag repr), and
            // supports multi-field and mixed-payload variants (per-variant in-register shapes under
            // one `Ty::Enum`) — all scratch-verified, cmtest w5_enum (1)-(8).
            //
            // FAIL-CLOSED admission gates (`register_enum` returns `None`): a variant field
            // that is not a seedable scalar (nested aggregate/ref/ptr — `enum_layout` sizing must
            // be PROVABLE, or a clean body's first construction would trap), a recursive enum
            // (cycle guard), an unresolvable discriminant assignment or one beyond the 64-bit
            // canonical tag cap, or a `#[repr(i128/u128)]` hint. Unions fall to the catch-all
            // (not `is_struct`, not `is_enum`).
            //
            // Trust (wave-EL, DATA-ENUM OPAQUE LANE): an enum `register_enum` declines is typed as the
            // OPAQUE LANE `Ty::Unit` — the same collapse `struct_ty_rmw_opaque` has always applied
            // to a data-enum SIBLING field, now uniform at the type level: the enum's payload is
            // never modeled; the value is a single opaque unit that FLOWS (param-bound, let-bound,
            // moved out of a field, passed to a call, inserted into a struct literal, returned).
            // This arm previously ALSO pushed a `Ty(enum-def)` tag with the same `Ty::Unit` result,
            // so every registration/lane a pre-wave walk produced is BYTE-IDENTICAL — only the tag
            // (the decline marker) is gone. Soundness is carried by the OPERATION arms, which all
            // gate on the mapped type and keep their own precise tags: construction (`EnumCtor(
            // non-enum mapped ty)`), match/payload extraction (`EnumMatch(non-enum mapped ty)` —
            // matching on a data enum's payload NEVER silently lowers), field writes (the chain-
            // assign leaf gates), scalar-only Deref/Cast/Binop. The admitted flows are exactly the
            // wave-EL lanes: the Field-arm opaque read (holder-lane-Unit proven), the
            // `opaque_local_aggregate_ty` local bind, the wave-MC receiver carrier, and the
            // `seed_constant_ty` struct-literal lane. An enum value only ever ARRIVES opaque
            // through those channels, so nothing downstream can observe a payload.
            // Trust (B3-2c T2): register_enum-OR-OPAQUE — the SOLE enum dispatch.
            // The legacy (I64, payload) tuple model is DELETED: every enum
            // register_enum admits (fieldless 2a, scalar-payload 2b, drop-free-ZST
            // 2c) is first-class Ty::Enum; everything it declines (niche/Ptr
            // payloads, enum-typed payloads, recursive adts, unresolvable/dup
            // discriminants, repr(i128)) falls to the fail-closed opaque floor.
            ty::Adt(adt, args) if adt.is_enum() => {
                if let Some(eid) = self.register_enum(*adt, *args) {
                    return Ty::Enum(eid);
                }
                // Trust (wave-SEAM): under `TRUST_OPTION_FLAG_LANES=1`, the OPTION lang
                // enum's opaque lane IS its DISCRIMINANT — `Ty::Bool`, uniformly.
                // Reaching here means register_enum declined = `is_opaque_lane_enum`
                // by construction. Every OTHER declined enum keeps the wave-EL
                // `Ty::Unit` collapse; flag off is byte-identical.
                if option_flag_lanes_enabled()
                    && self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(adt.did())
                {
                    Ty::Bool
                } else {
                    Ty::Unit
                }
            }
            // Trust: a SHARED SLICE reference `&[T]` → a FAT POINTER `Ty::Tuple([Ty::Ptr, Ty::I64])`
            // = `(data_ptr, len)`. This is the FAITHFUL slice representation (not a bare `Ty::Ptr`,
            // which would lose the length): the data pointer is the real in-memory address of an
            // `Alloca`'d + `Store`'d array (see the `PointerCoercion{Unsize}` arm), and `len` is the
            // element count as an `I64`. The pinned interpreter (c58fa68) materializes the tuple via
            // `Const`-seed + `InsertField` and round-trips the array through memory (`Ty::Tuple`
            // `byte_size`/`byte_align` + `Store`/`Load`), so `s[i]` (`GEP`+`Load` off field 0) and
            // `s.len()` (`ExtractField 1`) both interpret. Only IMMUTABLE `&[T]` is modeled; `&mut [T]`
            // falls through to the fail-closed catch-all (writing through a slice element needs a
            // store-through-fat-pointer model we do not have). The element type must itself be a
            // mappable scalar (a non-scalar elem records its own gap via the recursive `map_ty`).
            // Trust (B2-1, RFC TRUST_IR_V2): shared `&[T]` gets the FORMAT's first-class
            // fat-pointer spelling — `Ty::FatPtr(FatPtrKind::Slice(elem TyId))`, retiring
            // the anonymous `Tuple([Ptr, I64])` model for this class (the tuple ERASED the
            // element type; the fat kind carries it through the module `types` table). The
            // interpreter executes the value via PtrFromParts/PtrData/PtrMetadata + the
            // 16-byte two-lane memory image. `&str` deliberately KEEPS the tuple model
            // until the B2-2 recognizer rework (wave-Str/GH flip lanes pattern-match it);
            // `&mut [T]` stays thin below (write-through capability is a later slice).
            // An unmappable element fails the WHOLE type closed (its own gap tag + "Ty").
            ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                if matches!(pointee.kind(), ty::Slice(_)) =>
            {
                let ty::Slice(elem) = pointee.kind() else { unreachable!() };
                match self.map_ty_checked(*elem) {
                    Some(elem_mapped) => {
                        let tid = self.pend_ty(elem_mapped);
                        Ty::FatPtr(trust_ir::FatPtrKind::Slice(tid))
                    }
                    None => {
                        self.unsupported.push((format!("{ty:?}"), "Ty"));
                        Ty::Unit
                    }
                }
            }
            // Trust (wave-17): a SHARED `&str` reference → a FAT POINTER `Ty::Tuple([Ty::Ptr,
            // Ty::I64])` = `(data_ptr, len)`, EXACTLY the `&[u8]` slice shape above and the
            // MIR-side oracle's spelling: `trust_mir_extract` maps a rustc `&str` type to
            // `Ty::Ref{inner: Slice{u8}}` (convert.rs), and `trust_ir_bridge::lower`'s
            // `slice_fat_pointer_ty()` is `Tuple([Ptr, I64])` (lower.rs:175,269). So making the
            // producer emit the fat tuple ALIGNS it with the oracle's `&str` signature — it does
            // not introduce a new differential divergence. Field 0 is the byte data pointer (a
            // module-global `[u8; N]` address for a string LITERAL; the `ExprKind::Literal` arm
            // builds it), field 1 the byte length. Only IMMUTABLE `&str`; `&mut str` falls to the
            // generic ref arm below (thin `Ty::Ptr`) and any write-through stays fail-closed.
            // Trust (B2-2, RFC TRUST_IR_V2): shared `&str` gets the FORMAT's first-class
            // fat spelling — `Ty::FatPtr(FatPtrKind::Str)` (id-less; no types-table entry).
            // The oracle's FAITHFUL lane spells the same (`TrustTy::Str` -> bridge
            // FatPtr(Str)), so `tys_agree`'s (FatPtr, FatPtr) arm compares &str
            // signatures structurally. The legacy tuple model + its wave-Str/GH chain
            // recognizers retire in the SAME change (to_mir now matches the
            // PtrFromParts 3-node shape).
            ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                if matches!(pointee.kind(), ty::Str) =>
            {
                Ty::FatPtr(trust_ir::FatPtrKind::Str)
            }
            // Trust (B2-3, RFC TRUST_IR_V2): a SHARED `&dyn Trait` → the FORMAT's first-class
            // `Ty::FatPtr(FatPtrKind::TraitObject { trait_id })`, retiring the silent
            // ABI-UNFAITHFUL thin `Ty::Ptr` collapse (a `&dyn` is a 16-byte (data, vtable)
            // pair; the thin spelling dropped the vtable lane). `trait_id` is the CONTENT
            // hash of the principal trait's def path via the ONE shared mint
            // (`trust_ir::stable_trait_object_id`); the oracle bridge derives the SAME id
            // from the same `def_path_str` string, so `tys_agree` compares trait-object
            // positions by value with no table. Value capability this slice is WHOLE-VALUE
            // only (param hold + forward through the fat_shared_ref reborrow lane);
            // dispatch (forced-havoc bodyless decl since slice 2), unsize CONSTRUCTION
            // (needs a vtable global this producer cannot mint) and raw `*dyn` stay
            // fail-closed on their own arms. `&mut dyn` has NO arm of its own: it rides
            // the generic thin `&mut` arm below (fat_shape agrees Thin on both sides) —
            // a pre-existing 8-byte spelling of a 16-byte value, coherent but
            // unfaithful; the `&mut` fat-ref lane (the next B2 lever) retires it.
            // A PRINCIPAL-LESS trait object (`&dyn Send`) has no def path to hash — fail
            // closed rather than share a sentinel id (the oracle's `"dyn"` collapse class).
            ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                if matches!(pointee.kind(), ty::Dynamic(..)) =>
            {
                let ty::Dynamic(preds, ..) = pointee.kind() else { unreachable!() };
                match preds.principal_def_id() {
                    Some(principal) => match self.trait_object_id(principal) {
                        Some(trait_id) => {
                            Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { trait_id })
                        }
                        None => {
                            self.unsupported
                                .push((format!("{ty:?}"), "Ty(dyn trait-id collision)"));
                            Ty::Unit
                        }
                    },
                    None => {
                        self.unsupported.push((format!("{ty:?}"), "Ty(dyn no principal)"));
                        Ty::Unit
                    }
                }
            }
            // Trust: a SHARED reference `&T` → `Ty::Ptr` (the memory-model foothold). The trust-ir
            // interpreter is allocation-aware: `Ty::Ptr` is the opaque pointer a `Borrow` materializes
            // via `Alloca`+`Store` and a `Deref` consumes via `Load` (see the `ExprKind::Borrow`/
            // `Deref` arms). Mirrors the MIR-bridge oracle, which maps `Ty::Ref → Ty::Ptr` too. Both
            // shared (`Mutability::Not`) AND mutable (`Mutability::Mut`) map to `Ty::Ptr`: a `&mut T`
            // is the slot pointer of a memory-PROMOTED local (the `&mut`-borrowed local lives in a
            // single `Alloca` slot for its whole lifetime; see the `promoted` field + the
            // `ExprKind::Borrow{Mut}` / `*r = v` arms). Raw pointers / fn pointers are deliberately
            // NOT mapped here (still fail-closed). The `&[T]` slice ref is handled by the arm ABOVE.
            ty::Ref(_, _, rustc_hir::Mutability::Not | rustc_hir::Mutability::Mut) => Ty::Ptr,
            // Trust: a THIN raw pointer `*const T` / `*mut T` → `Ty::Ptr`, as an OPAQUE value.
            // This is exactly the MIR-side oracle's convention (`trust_mir_extract` converts
            // `TyKind::RawPtr → TrustTy::RawPtr` and the bridge's `map_type` sends any
            // non-slice-pointee `Ty::RawPtr { .. } → TrustIrTy::Ptr`, lower.rs:175-177), so the
            // differential signatures agree. Admitting the TYPE adds no operation semantics:
            // every raw-pointer OPERATION stays fail-closed on its own arm (deref → `Deref(non-
            // borrow ptr)`, `&raw` → the `ExprKind` catch-all, ptr casts → `Cast(non-int
            // source/dest)`, ptr-typed call args → the borrow-ptr/arg gates), and a raw-ptr
            // PARAM that is actually READ is refused by the differential's opacity proof
            // (`param_never_read`), so no execution path ever assigns meaning to the pointee.
            // Trust (totality Batch A): FAT raw pointers get PARITY with the oracle's
            // spelling instead of a blanket fail-closed wall.
            //  * `*const [T]` / `*const str`: the `(data_ptr, len)` pair — the SAME
            //    `Tuple([Ptr, I64])` shape the `&[T]`/`&str` ref arms use, and exactly
            //    what the oracle signs for a slice-pointee raw ptr
            //    (trust-ir-bridge lower.rs:186, `slice_fat_pointer_ty()`).
            //  * `*const [T; N]`, THREE-WAY on the length (mirrors ty_convert.rs:493-524
            //    at the trust-types level):
            //      - concrete `N` → THIN `Ty::Ptr` (oracle pointee spelling `Array` →
            //        thin, lower.rs:187);
            //      - const-generic `ConstKind::Param` → FAT pair (oracle spelling
            //        `SymArray` → slice fat pointer, lower.rs:184);
            //      - anything else (unevaluated named const, …) keeps the precise
            //        fail-closed tag: emitting fat would MANUFACTURE a fat-vs-thin
            //        signature divergence on `*const [u8; NAMED_CONST]`.
            //    Deliberately NO `try_normalize_erasing_regions` fallback here: unlike
            //    ty_convert (which runs post-borrowck in `optimized_mir`), this producer
            //    runs INSIDE `mir_built`, where normalizing an unevaluated const can
            //    demand CTFE → the const's own MIR → the E0391 reentrancy class the
            //    cycle_safe guards exist to prevent.
            ty::RawPtr(pointee, _) => match pointee.kind() {
                ty::Slice(_) | ty::Str => Ty::Tuple(vec![Ty::Ptr, Ty::I64]),
                ty::Array(_, n) => match (n.try_to_target_usize(self.tcx), n.kind()) {
                    (Some(_), _) => Ty::Ptr,
                    (None, ty::ConstKind::Param(_)) => Ty::Tuple(vec![Ty::Ptr, Ty::I64]),
                    (None, _) => {
                        self.unsupported.push((format!("{ty:?}"), "Ty(raw-ptr fat/array pointee)"));
                        Ty::Unit
                    }
                },
                // Trait-object raw pointers are fat too, but this producer does not
                // yet carry the vtable component. Never silently respell them thin.
                ty::Dynamic(..) => {
                    self.unsupported.push((format!("{ty:?}"), "Ty(raw-ptr fat/array pointee)"));
                    Ty::Unit
                }
                _ => Ty::Ptr,
            },
            // Trust: a FIXED-SIZE array `[T; N]` → a `Ty::Tuple([T; N])` of N identical (recursively
            // mapped) element types. We do NOT use `Ty::Array(TyId, N)`: that needs an interned `TyId`
            // this single-function producer never mints, whereas a `Ty::Tuple` of the element type is
            // built directly and the pinned interpreter materializes it from a `Const`-seeded aggregate
            // (the exact tuple/struct machinery). Construction (`ExprKind::Array`/`Repeat`) and indexing
            // (`ExprKind::Index`) operate over this tuple aggregate via `InsertField`/`ExtractField`/
            // `ExtractElement`.
            //
            // FAIL-CLOSED: a non-const length (a generic const param `[T; N]` whose `N` is not a
            // concrete usize — `try_to_target_usize` returns `None`), or a non-scalar element type whose
            // recursive `map_ty` records its own gap (the construction/index arms then reject it via
            // `seed_constant`/`is_scalar_ty`). Slices `[T]` are NOT `ty::Array`, so they never reach here
            // (they fall to the fail-closed catch-all below).
            ty::Array(elem, len) => {
                let n = match len.try_to_target_usize(self.tcx) {
                    Some(n) => n as usize,
                    None => {
                        self.unsupported.push((format!("{ty:?}"), "Ty(array non-const len)"));
                        return Ty::Unit;
                    }
                };
                let elem_ty = self.map_ty(*elem);
                // Trust: ZERO-LENGTH `[T; 0]` → `Ty::Array(TyId, 0)` over a pended module-types
                // entry — the MIR-side oracle's exact spelling (`map_type_ctx` Array arm), and
                // materializable: the pinned interpreter converts `(Ty::Array, Constant::Array)`
                // with a length check (scratch-verified, cmtest w4_struct (5)). The old
                // `Ty::Tuple([])` spelling was a guaranteed signature divergence ('THIR
                // []->[Tuple([])] vs MIR []->[Array(TyId(0), 0)]', 3 ui bodies). A fn-ptr
                // element type stays fail-closed: the splice's `TyId` re-interning is
                // deliberately non-recursive into `func_types` (mirrors `ty_contains_func`).
                if n == 0 {
                    if ty_contains_func(&elem_ty) {
                        self.unsupported.push((format!("{ty:?}"), "Ty(array elem fn-ptr)"));
                        return Ty::Unit;
                    }
                    return Ty::Array(self.pend_ty(elem_ty), 0);
                }
                Ty::Tuple(vec![elem_ty; n])
            }
            // Trust: a FUNCTION POINTER `fn(…) -> …` → `Ty::Func(sig)` over a pended per-body
            // `FuncTy` (see `map_fn_ptr_ty` for the admitted fragment and `pending_func_tys`
            // for the id convention). The VALUE inhabiting it is only ever produced by the
            // `ReifyFnPointer` arm (`Inst::Const { ty: Ty::Func(_), value: Constant::FnDef }`)
            // and only ever CONSUMED by `Inst::CallIndirect` — the two positions crate-level
            // splicing checks and remaps. Everything else that could carry a `Ty::Func` into
            // the assembled module (a fn-ptr param/return in the signature, a merge block
            // param, a struct field) is refused by `splice_ok`'s existing table-free checks,
            // and aggregate CONSTRUCTION over `Ty::Func` fields fails closed at the seed
            // (`seed_constant` has no `Func` arm) — the containment that keeps the splice
            // remap non-recursive.
            ty::FnPtr(sig_tys, header) => match self.map_fn_ptr_ty(*sig_tys, *header) {
                Some(t) => t,
                None => {
                    self.unsupported.push((format!("{ty:?}"), "Ty(fn-ptr)"));
                    Ty::Unit
                }
            },
            // Trust: a PATTERN TYPE (`pattern_type!(usize is 0..=N)`, the niche carrier inside
            // `NonZero<T>`/`UsizeNoHighBit`/…) → the BASE scalar type, recursively mapped. The
            // pattern is a range REFINEMENT of the base type: every value inhabiting the pattern
            // type is a value of the base type with identical bits/layout, so widening is sound
            // for lowering (any trap-freedom that holds on the full-range base holds on the
            // restricted subset, and no MIR-level operation this fragment lowers depends on the
            // refinement). This is byte-for-byte the MIR-side ORACLE's convention:
            // `trust_mir_extract::ty_convert` `TyKind::Pat(inner_ty, _pat) =>
            // convert_ty_inner(tcx, *inner_ty, ctx)` (ty_convert.rs:683) — reached unconditionally
            // from `extract_function` (the `supportability::classify` Pat fast-reject is the
            // crate-level advisory classifier, NOT on the extraction path) — so the differential
            // signatures agree. A base type that is itself unmappable records its own gap via the
            // recursive `map_ty`. The FLIP still refuses pattern-typed ABI-visible decls
            // fail-closed via its exact rustc-type equality (same containment as `char`/`u32`).
            ty::Pat(base, _) => self.map_ty(*base),
            // Trust: an ALIAS type (`ty::Alias` — projection `<C as Trait>::Assoc`, inherent
            // alias, lazy/free alias) → NORMALIZE to the underlying concrete type via
            // `try_normalize_erasing_regions` under `TypingEnv::fully_monomorphized()` — the
            // exact `resolve_callee` precedent (see ~:957, the `CheckCallRecursion`-sanctioned
            // reentrancy-safe seam inside `mir_built`) — and RE-ENTER `map_ty` on the result, so
            // the mapped spelling is identical to writing the concrete type directly.
            //
            // FAIL-CLOSED (unchanged catch-all "Ty" tag), never a guess:
            //   * params/infer in the alias (`has_non_region_param`/`has_non_region_infer`) —
            //     `fully_monomorphized` requires param-free input; a generic body's
            //     `<T as Trait>::Assoc` stays fail-closed by design until mono (the T/#0 bucket);
            //   * OPAQUE types anywhere (`has_opaque_types`) — normalizing an RPIT/async opaque
            //     from inside `mir_built` can demand the opaque's hidden type, whose computation
            //     needs borrowck of the DEFINING body: an E0391 query cycle when (mutually)
            //     recursive (the `resolve_callee` opaque guard's exact rationale);
            //   * escaping bound vars (defensive — normalization requires a fully bound value);
            //   * normalization Err, or an output still `ty::Alias` at the top level (also covers
            //     the `norm == ty` fixpoint) — re-entry only happens on a genuinely resolved,
            //     non-alias head, so the recursion terminates (any REMAINING nested alias in the
            //     result re-enters this arm on a strictly smaller type and fails closed at its
            //     own fixpoint).
            ty::Alias(..) => {
                if ty.has_non_region_param()
                    || ty.has_non_region_infer()
                    || ty.has_opaque_types()
                    || ty.has_escaping_bound_vars()
                {
                    self.unsupported.push((format!("{ty:?}"), "Ty"));
                    return Ty::Unit;
                }
                let typing_env = ty::TypingEnv::fully_monomorphized();
                // Trust: rust 1.99 — `try_normalize_erasing_regions` takes `Unnormalized<T>`;
                // wrap the materialized value with `new_wip` (compiler-idiomatic).
                match self
                    .tcx
                    .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(ty))
                {
                    Ok(norm) if !matches!(norm.kind(), ty::Alias(..)) => self.map_ty(norm),
                    _ => {
                        self.unsupported.push((format!("{ty:?}"), "Ty"));
                        Ty::Unit
                    }
                }
            }
            // Trust (wave-CF): a CAPTURING closure type appears as the type of a closure LOCAL
            // (`let f = || …`) — never a signature position (a closure-typed param/return is a
            // generic `F: Fn` / opaque `impl Fn`, refused earlier by the `ty::Param`/`Alias`
            // opaque gates). Model a thin-capturing closure as its ENV TUPLE `Ty::Tuple(captures)`
            // (capture order = field index) — the SAME model wave-CE's `UpvarRef` read side and
            // the `ExprKind::Closure` value arm use, so the closure-local's declared type matches
            // the constructed env value. Gate to a NON-EMPTY, ALL-THIN capture list (`upvar_is_thin`
            // — scalar / thin ptr): a capture-free closure (wave-5 skips its binding) and a
            // fat/aggregate/Drop/nested-closure capture keep the fail-closed `"Ty"` tag below,
            // so nothing that was clean changes and no non-tuple env is ever minted.
            ty::Closure(_, cargs) => {
                let clo = cargs.as_closure();
                let upvar_tys = clo.upvar_tys();
                if upvar_tys.is_empty() || !upvar_tys.iter().all(|t| self.upvar_is_thin(t)) {
                    self.unsupported.push((format!("{ty:?}"), "Ty"));
                    Ty::Unit
                } else if matches!(clo.kind(), ty::ClosureKind::FnOnce) {
                    // Trust (B6, v25 Fn/ByValue slice): a by-value-env (FnOnce-kind)
                    // capturing closure gets the FORMAT's first-class spelling —
                    // `Ty::Closure(ClosureTyId)` over `ClosureTy { func, captures }`.
                    // The env value never transits memory (the caller passes it as
                    // arg 0, the callee field-reads the param), so the register-level
                    // interpreter lane suffices. Fn/FnMut (by-REF env) closures KEEP
                    // the tuple spelling below until the v26 kind/capture-mode fields
                    // exist — their memory-transit lanes depend on it, and the mode
                    // distinction is unrepresentable in the v25 `ClosureTy`.
                    match self.closure_first_class_ty(clo) {
                        Some(t) => t,
                        None => {
                            self.unsupported.push((format!("{ty:?}"), "Ty"));
                            Ty::Unit
                        }
                    }
                } else {
                    Ty::Tuple(upvar_tys.iter().map(|t| self.map_ty(t)).collect())
                }
            }
            _ => {
                self.unsupported.push((format!("{ty:?}"), "Ty"));
                Ty::Unit
            }
        }
    }

    /// Trust (wave-CF): is a closure CAPTURE type "thin" — mappable to a scalar or a THIN
    /// `Ty::Ptr` — so the env tuple `Ty::Tuple(captures)` is table-free/spliceable and every
    /// field read/insert is well-formed? A scalar (bool/char/int/float) OR a ref/raw-ptr with a
    /// THIN pointee (mirrors [[maptyx-collapses-fat-refs-to-thin-ptr]]: `&str`/`&[T]`/`&dyn`/
    /// `&extern-type` are FAT and refused). Everything else (aggregates, nested closures,
    /// generics, `!`) is NOT thin. Pure (no `map_ty` side effects), so a REJECTED closure never
    /// spuriously registers a capture's inner struct/enum.
    fn upvar_is_thin(&self, t: RustcTy<'tcx>) -> bool {
        let thin_pointee = |p: RustcTy<'tcx>| {
            !matches!(p.kind(), ty::Str | ty::Slice(_) | ty::Dynamic(..) | ty::Foreign(_))
        };
        match t.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
            ty::Ref(_, pointee, _) => thin_pointee(*pointee),
            ty::RawPtr(pointee, _) => thin_pointee(*pointee),
            _ => false,
        }
    }

    /// Trust (B6): the FORMAT's first-class type for a by-value-env (FnOnce-kind) capturing
    /// closure — `Ty::Closure(id)` over `ClosureTy { func: the closure's CALL signature,
    /// captures }`. The signature comes from `clo.sig()` (inputs = one tuple of the call
    /// arguments, no env — untupled here into `FuncTy::params`; unit return = empty
    /// `returns`, the producer's convention). Every component maps through `map_ty` with the
    /// failure channel — one unmappable arg/return/capture declines the WHOLE closure type
    /// (`None` → the caller's fail-closed tag), never a partial spelling. Captures are
    /// gate-checked thin by the caller (`upvar_is_thin`), so the `ClosureTy` is table-free
    /// in its captures by construction — `splice_ok` re-checks, never assumes.
    fn closure_first_class_ty(&mut self, clo: ty::ClosureArgs<TyCtxt<'tcx>>) -> Option<Ty> {
        let sig = clo.sig();
        let sig = self.tcx.instantiate_bound_regions_with_erased(sig);
        let inputs = sig.inputs();
        let ty::Tuple(arg_tys) = inputs.first()?.kind() else { return None };
        let mut params = Vec::with_capacity(arg_tys.len());
        for a in arg_tys.iter() {
            params.push(self.map_ty_checked(a)?);
        }
        let returns = if sig.output().is_unit() {
            Vec::new()
        } else {
            vec![self.map_ty_checked(sig.output())?]
        };
        let mut captures = Vec::with_capacity(clo.upvar_tys().len());
        for c in clo.upvar_tys().iter() {
            captures.push(self.map_ty_checked(c)?);
        }
        let func = self.pend_func_ty(FuncTy { params, returns, is_vararg: false });
        Some(Ty::Closure(self.pend_closure_ty(trust_ir::ClosureTy { func, captures })))
    }

    /// Trust: the closure-ENVIRONMENT param type for a closure body, or `None` for a non-closure
    /// body (free/assoc fn — no env param exists). See the convention comment in `lower_fn`.
    ///
    /// Matches the MIR-side oracle's signing of the same body exactly
    /// (`trust_mir_extract::ty_convert` + `trust_ir_bridge::lower::map_type{,_ctx}`):
    ///   * `Fn`/`FnMut` env `&{closure}` / `&mut {closure}` — a THIN ref; the oracle converts
    ///     `TyKind::Ref → TrustTy::Ref → TrustIrTy::Ptr`. We sign `Ty::Ptr`.
    ///   * `FnOnce` by-value NON-capturing env — the oracle converts `TyKind::Closure` (empty
    ///     `upvar_tys`) `→ TrustTy::Closure { upvars: [] } → TrustIrTy::Unit`. We sign `Ty::Unit`.
    ///
    /// FAIL-CLOSED (precise tag + placeholder `Ty::Unit`, so the module stays well-formed while
    /// the ratchet reports the body as unsupported):
    ///   * coroutine bodies (`tcx.is_coroutine`) — their THIR params are `[coroutine-by-value,
    ///     resume]` and the oracle signs the state-machine convention; do not guess.
    ///   * a by-value CAPTURING env — the oracle signs it `TrustIrTy::Struct(id)` (a first-class
    ///     struct), which this producer's `Ty::Tuple` aggregate convention cannot equal.
    ///   * anything else (incl. a closure body whose THIR unexpectedly lacks the pat-less
    ///     `params[0]` env slot).
    fn closure_env_param_ty(&mut self, def: LocalDefId) -> Option<Ty> {
        if self.tcx.def_kind(def) != rustc_hir::def::DefKind::Closure {
            return None;
        }
        if self.tcx.is_coroutine(def.to_def_id()) {
            // Trust (wave-CO): a YIELD-FREE, NON-CAPTURING coroutine (`async fn nop(){}`, `async {}`,
            // `async move { 22u32 }`) has an empty frame that never suspends — no captured upvars to
            // carry and no live-across-suspend state to preserve. Sign its self/env as `Ty::Unit`
            // (the SAME placeholder the tagged path already returns) WITHOUT pushing the fail-closed
            // tag. This is a pure SCORECARD-tag suppression: the lowered IR is byte-identical to
            // today (same `Ty::Unit` env, same straight-line body — the corpus bodies carry ONLY this
            // tag), so the flip/differential gate sees the same module and the flip decision is
            // UNCHANGED (+0 flip). Yield detection is SOUND: `.await` desugars to `hir::ExprKind::Yield`
            // in ast-lowering (`rustc_ast_lowering::expr::lower_expr_await`), which THIR building maps
            // to `ExprKind::Yield` (`rustc_mir_build::thir::cx::expr`), so ANY await or explicit yield
            // leaves a `Yield` in this body's THIR. A SUSPENDING or CAPTURING coroutine keeps the tag
            // (its real state-machine frame is not a Unit env).
            let yield_free =
                !self.thir.exprs.iter().any(|e| matches!(e.kind, ExprKind::Yield { .. }));
            let non_capturing = self
                .thir
                .params
                .iter()
                .next()
                .filter(|p| p.pat.is_none())
                .map(|p| {
                    matches!(
                        p.ty.kind(),
                        ty::Coroutine(_, cargs) if cargs.as_coroutine().upvar_tys().is_empty()
                    )
                })
                .unwrap_or(false);
            // Restrict to ASYNC coroutines. An async coroutine's resume param is `ResumeTy`
            // (`NonNull<Context>` → `Ty::Struct`), a NON-scalar the interpreter differential opacity
            // gate refuses → the body is forced `NotRun` BEFORE any signature comparison, so the
            // `Unit`-env producer sig vs the oracle's `Struct(zero-field)` coroutine-env sig is never
            // compared → 0 new divergence. A non-async coroutine (`gen {}`, bare `#[coroutine] || {}`)
            // has resume type `()` → params `[Unit, Unit]` reach the signature comparison and would
            // record a NEW `MirOracle` divergence (`Unit` vs `Struct`). All corpus coroutine bodies
            // are async, so this restriction costs 0 yield and closes that hole fail-closed.
            let is_async = matches!(
                self.tcx.coroutine_kind(def.to_def_id()),
                Some(rustc_hir::CoroutineKind::Desugared(rustc_hir::CoroutineDesugaring::Async, _))
            );
            if yield_free && non_capturing && is_async {
                return Some(Ty::Unit);
            }
            self.unsupported.push(("body".to_string(), "ClosureEnv(coroutine body)"));
            return Some(Ty::Unit);
        }
        let Some(env) = self.thir.params.iter().next().filter(|p| p.pat.is_none()) else {
            self.unsupported.push(("body".to_string(), "ClosureEnv(missing THIR env param)"));
            return Some(Ty::Unit);
        };
        match env.ty.kind() {
            // `closure_env_ty` for `Fn`/`FnMut`: a thin `&{closure}` / `&mut {closure}`.
            ty::Ref(..) => Some(Ty::Ptr),
            // `closure_env_ty` for `FnOnce`: the closure type itself, by value.
            ty::Closure(_, args) if args.as_closure().upvar_tys().is_empty() => Some(Ty::Unit),
            // Trust (B6, v25 Fn/ByValue slice): a CAPTURING by-value env — sign the
            // closure's first-class `Ty::Closure` spelling (map_ty's kind-split; a
            // by-value env implies FnOnce kind, so the split always takes the
            // first-class arm here). The UpvarRef lane field-reads this param
            // directly (no memory transit). A closure the split cannot spell
            // (non-thin capture, unmappable sig) keeps the fail-closed tag.
            ty::Closure(..) => {
                let mapped = self.map_ty(env.ty);
                if matches!(mapped, Ty::Closure(_)) {
                    Some(mapped)
                } else {
                    self.unsupported
                        .push((format!("{:?}", env.ty), "ClosureEnv(by-value captures)"));
                    Some(Ty::Unit)
                }
            }
            _ => {
                self.unsupported.push((format!("{:?}", env.ty), "ClosureEnv(by-value captures)"));
                Some(Ty::Unit)
            }
        }
    }

    /// Trust: ledger a callee/target `DefId` and return its DefIndex-derived `FuncId` (see
    /// `Lowered::callees`). The `FuncId` is a structural reference only (never used to index this
    /// single-function module), so cross-crate index collisions are irrelevant here. They DO
    /// matter to crate-level assembly (`crate_module`), so every admitted identity is recorded.
    /// Dedup on FULL identity only: the same callee referenced twice records once, but a
    /// local/extern index collision keeps both entries so `crate_module` sees the ambiguity and
    /// fails closed instead of mis-linking.
    fn admit_callee(&mut self, def_id: DefId) -> FuncId {
        self.admit_callee_inner(def_id, false, None)
    }

    /// Trust (wave-20): admit a callee edge that crate assembly must FORCE to a bodyless HAVOC
    /// declaration (never link to a local body). Used for a GENERIC (`has_non_region_param`) call
    /// whose polymorphic target cannot faithfully link to any single identity-lowered record.
    fn admit_havoc_callee(&mut self, def_id: DefId) -> FuncId {
        self.admit_callee_inner(def_id, true, None)
    }

    /// Trust (wave-C): admit a concrete-monomorphic callee, recording the SITE identity
    /// (`site_def_id`, `site_args`) that built MIR spells so the shim can flip the call body.
    /// `assembly_def_id` remains the crate-assembly identity (`FuncId`/dedup); for a free fn /
    /// inherent method it equals `site_def_id`, for a trait method it is the resolved-instance
    /// DefId (unchanged from the pre-wave-C admit) while `site_def_id` is the trait method.
    fn admit_callee_site(
        &mut self,
        assembly_def_id: DefId,
        site_def_id: DefId,
        site_args: ty::GenericArgsRef<'tcx>,
    ) -> FuncId {
        let enc = encode_site_args(self.tcx, site_args);
        self.admit_callee_inner(assembly_def_id, false, Some((site_def_id, enc)))
    }

    fn admit_callee_inner(
        &mut self,
        def_id: DefId,
        force_havoc: bool,
        site: Option<(DefId, Option<Vec<SiteArg>>)>,
    ) -> FuncId {
        let func_id = FuncId::new(def_id.index.as_u32());
        let is_local = def_id.is_local();
        // The SITE identity built MIR spells (wave-C). Absent (closure/reify/havoc admits) ⇒ the
        // site is the assembly `def_id` with UN-encodable args (`None`) → the shim fails closed,
        // exactly the pre-wave-C behavior for those non-flippable callees.
        let (site_def_id, site_args) = match site {
            Some((s, a)) => (s, a),
            None => (def_id, None),
        };
        // Trust: `with_no_trimmed_paths!` — a bare `def_path_str` arms the
        // `trimmed_def_paths` query's `must_produce_diag` invariant, which ICEs at
        // `DiagCtxt` drop on any warning-free compile (the check is skipped when
        // RUSTC_LOG is set, which is why log-capturing probes never see it).
        let def_path =
            rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(def_id));
        // Trust (wave-6): `def_id` joined the dedup key — a pure STRENGTHENING (an entry pair
        // differing only in `def_id` now stays as two entries, which downstream consumers —
        // `crate_module::resolve_callee` and the shim's `to_mir` Call lowering — treat as an
        // ambiguous FuncId and fail closed instead of guessing). Trust (wave-20): `force_havoc`
        // also joins the key so a havoc edge never coalesces with a real link to the same DefId.
        // Trust (wave-C): `site_def_id`/`site_args` join the key so two distinct monomorphizations
        // of one DefId (`id::<i32>(a); id::<u8>(b)`) stay as two entries under the same `FuncId` →
        // the shim's ambiguity rule fails the whole body closed (bounded, no FuncId rework).
        if !self.callees.iter().any(|c| {
            c.func_id == func_id
                && c.is_local == is_local
                && c.def_id == def_id
                && c.def_path == def_path
                && c.force_havoc == force_havoc
                && c.site_def_id == site_def_id
                && c.site_args == site_args
        }) {
            self.callees.push(CalleeRef {
                func_id,
                is_local,
                def_index: def_id.index.as_u32(),
                def_id,
                def_path,
                force_havoc,
                site_def_id,
                site_args,
            });
        }
        func_id
    }

    /// Resolve a THIR call's function operand. Three outcomes, all PROVEN or fail-closed:
    ///
    ///   * `Ok(CalleeKind::Direct(FuncId))` — a statically-known callee `DefId`:
    ///       - the original path: an explicit HIR call (`from_hir_call`) to a `DefKind::Fn`
    ///         free function (admitted WITHOUT instance resolution, exactly as before — the
    ///         DefIndex identity + ledger convention);
    ///       - NEW: a method (`DefKind::AssocFn`, `x.foo()` / UFCS) or an overloaded-operator
    ///         desugar (`from_hir_call == false`, e.g. `a + b` on a user `Add` impl), resolved
    ///         to its CONCRETE instance via `ty::Instance::try_resolve` — the same call rustc's
    ///         own `CheckCallRecursion` lint performs inside the very same `mir_built` query
    ///         (compiler/rustc_mir_transform/src/check_call_recursion.rs:150), which is the
    ///         reentrancy-safety precedent for resolving at this seam. Only a plain resolved
    ///         `InstanceKind::Item` that is neither closure-like nor a trait-default body is
    ///         admitted; the receiver is just arg 0 (THIR has already UFCS-rewritten it).
    ///   * `Ok(CalleeKind::FnPtr(fun))` — the (peeled) operand is a VALUE of `ty::FnPtr` type:
    ///     an indirect call. The caller lowers the value and emits `Inst::CallIndirect`.
    ///   * `Ok(CalleeKind::ClosureCall { callee, capturing })` — a rust-call-ABI
    ///     `Fn`/`FnMut::call{,_mut}` that resolved to `InstanceKind::Item` of a LOCAL,
    ///     non-coroutine closure body (`resolve_fn_trait_callee`): the caller UNTUPLES the args
    ///     and supplies the env param — a fresh unit-slot Ptr when `!capturing`, or (wave-CF) the
    ///     address of the materialized `Ty::Tuple(captures)` env when `capturing`.
    ///   * `Err(tag)` — fail-closed with a PRECISE split tag (pushed by the caller):
    ///       - "Call(generic callee)":   unsubstituted params in the callee args (generic
    ///         caller — incl. an `F: Fn(…)` bound's `f(x)`), or resolution returned `Ok(None)`
    ///         (can't know what runs);
    ///       - "Call(dyn dispatch)":     a `dyn Fn*` receiver on the rust-call path (the
    ///         call SITE commits to an untupled-args ABI no unknowable virtual callee can
    ///         back), or the defensive `Virtual` redirect tripwire. Plain-ABI
    ///         `InstanceKind::Virtual` calls route to the wave-20 forced-havoc lane
    ///         instead (B2-3 slice 2) — bodyless decl, never linked, never flipped;
    ///       - "Call(trait default)":    resolved to the trait's own default body (its lowering
    ///         is Self-generic; linking the identity-lowered record would be a guess);
    ///       - "Call(closure call)":     resolved to a closure-like body OUTSIDE the supported
    ///         `ClosureCall` shape (non-local closure, coroutine, or a closure Item reached via
    ///         a non-rust-call sig — defensive: never linked, the untupling/env conventions
    ///         would be a lie);
    ///       - "Call(closure env unsupported)": `Fn*::call*` resolved to a LOCAL closure body
    ///         whose env the call site cannot rebuild faithfully — a CAPTURING closure (its env
    ///         value must alias the closure's capture frame, which closure construction does
    ///         not lower yet), a by-value `FnOnce` env (unreachable for non-capturing closures
    ///         — kind inference yields `Fn`; kept as a tripwire), or a receiver expr not proven
    ///         effect-free (discarding it would drop effects);
    ///       - "Call(closure untuple unsupported)": the supported closure callee's tupled-args
    ///         operand is not a literal tuple and could not be lowered + `ExtractField`-split
    ///         (see `lower_closure_call_untupled`);
    ///       - "Call(rust-call ABI)":    residual `extern "rust-call"` shapes — a non-`Fn*`
    ///         rust-call def, or a `Fn*::call*` receiver that is not a plain closure/`dyn`
    ///         (fn-def/fn-ptr receivers resolve to `FnPtrShim`s, coroutine-closures to their
    ///         own shims — synthetic MIR we do not model);
    ///       - "Call(intrinsic)":        `InstanceKind::Intrinsic` (no callable body — magic);
    ///       - "Call(instance shim)":    any other `InstanceKind` (Reify/FnPtr/Clone/drop-glue
    ///         shims… — synthetic MIR we do not model);
    ///       - "Call(resolution error)": `Err(ErrorGuaranteed)` from resolution;
    ///       - "Call(ctor)":             tuple-struct/variant constructor call (an aggregate
    ///         build, not a call edge — separate lowering, not modeled yet);
    ///       - "Call(unsupported callee def-kind)" / "Call(indirect non-fn-ptr callee)": rest.
    ///     For operator-position calls (`from_hir_call == false`) EVERY failure collapses to the
    ///     single split tag "Call(operator)" — the measured bucket the ratchet tracks.
    ///
    /// Trust (wave-19): is admitting the callee `callee` at substitution `args` ABI-COHERENT with its
    /// IDENTITY-lowered crate-module record? The record was lowered at IDENTITY args, where `map_ty`
    /// signs a `&T` whose (normalized) pointee is NOT a concrete slice/str (incl. `&Self`, `&Param`,
    /// `&Self::Assoc`) as a THIN `Ty::Ptr`. A concrete monomorphization that turns such a position —
    /// AT ANY NESTING DEPTH: top-level, behind a projection, or inside a tuple/array/struct/enum —
    /// into a FAT `&str`/`&[T]` reference is ABI-INCOHERENT: linking the fat caller arg/return to the
    /// thin record slot drops the DST length lane (a real soundness hole — adversarially confirmed,
    /// including the NESTED `(&U,i32)`→`(&str,i32)` and struct-wrapped `Wrap<T>`→`Wrap<str>` forms
    /// that a top-level-only pointer-class check missed). Compare the recursive [`FatShape`] of every
    /// input+output position between the identity and the concrete signature.
    ///
    /// SKIP two classes of position, both sound:
    ///  - a NON-LOCAL callee is never spliced (no THIR here) → always a HAVOC extern → any
    ///    instantiation links soundly; return `true` without inspecting the sig (and don't regress
    ///    the pre-existing clean cross-crate/`std` calls to a fail-closed).
    ///  - an `Opaque` IDENTITY position: `map_ty` failed closed on it during the callee's OWN
    ///    lowering → the callee body is DIRTY → a HAVOC extern → the position imposes no coherence
    ///    constraint (this preserves the "a call to a fail-closed callee stays clean" behavior).
    ///
    /// A param/alias that stays generic in BOTH signatures (a generic caller forwarding its own
    /// `?Sized` param, e.g. `fn w<T:?Sized>(x:&T){ id::<T>(x) }`) is `Thin`==`Thin` (or `Opaque` by
    /// value) on both sides → admitted; this is sound because any UNSIZED concrete instantiation of
    /// the OUTER caller is itself rejected at that outer call site (the gate runs at every site), so
    /// a fat value can never actually reach the thin slot. Side-effect-free (no `map_ty`, no interning).
    fn sig_shapes_coherent(
        &self,
        callee: rustc_span::def_id::DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> bool {
        if !callee.is_local() {
            return true;
        }
        let tcx = self.tcx;
        // Trust: rust 1.99 — `EarlyBinder::instantiate*` return `Unnormalized<T>`; unwrap with
        // `.skip_normalization()` (the shape comparison below is structural, exactly as before).
        let ident = tcx.instantiate_bound_regions_with_erased(
            tcx.fn_sig(callee).instantiate_identity().skip_normalization(),
        );
        let conc = tcx.instantiate_bound_regions_with_erased(
            tcx.fn_sig(callee).instantiate(tcx, args).skip_normalization(),
        );
        let iu = ident.inputs_and_output;
        let cu = conc.inputs_and_output;
        if iu.len() != cu.len() {
            return false;
        }
        iu.iter().zip(cu.iter()).all(|(i, c)| {
            let si = self.fat_shape(i, &mut Vec::new());
            // An Opaque identity position → the callee is havoc → no constraint. Otherwise the
            // concrete shape must equal the identity shape; a concrete `Opaque` (e.g. a fat raw
            // pointer the caller could not have constructed cleanly anyway) is `!= si`, so it fails
            // closed — sound.
            si == FatShape::Opaque || si == self.fat_shape(c, &mut Vec::new())
        })
    }

    /// Trust (wave-19): PURE recursive `map_ty` fatness classifier — see [`FatShape`]. Normalizes each
    /// type (and each ref pointee) under `fully_monomorphized` so a concrete projection
    /// (`&<i32 as Tr>::Assoc`) resolves to its fat form (`&str`) before classification, while an
    /// identity alias (`&<Self as Tr>::Assoc`) stays unresolved and classifies `Thin` — the exact
    /// asymmetry that makes an associated-type-projection fatness flip visible. Mirrors the fatness
    /// arms of `map_ty` (lib.rs:~692-780); `visited` cycle-guards recursive adts exactly as
    /// `map_ty`/`struct_field_tys` do (an unguarded fixpoint is a stack-overflow SIGBUS, not an error).
    fn fat_shape(
        &self,
        ty: RustcTy<'tcx>,
        visited: &mut Vec<(rustc_span::def_id::DefId, ty::GenericArgsRef<'tcx>)>,
    ) -> FatShape {
        let tcx = self.tcx;
        let te = ty::TypingEnv::fully_monomorphized();
        let norm = |t: RustcTy<'tcx>| cycle_safe_normalize(tcx, te, t);
        let ty = norm(ty);
        match ty.kind() {
            // `!` included: map_ty gives the zero-width first-class `Ty::Never` (Batch A) —
            // no pointer indirection, scalar-class for fatness purposes.
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => {
                FatShape::Scalar
            }
            // Shared ref: FAT iff the (normalized) pointee is slice/str (map_ty:703/720); else THIN.
            // Deliberately does NOT inspect the slice ELEMENT: map_ty's slice arm ERASES it (lib.rs:739
            // discards `map_ty(*elem)`, always emitting `Tuple([Ptr,I64])`), so the record slot is
            // element-independent — an `&[&T]`→`&[&str]` element flip yields a bit-identical slot and
            // is unobservable (non-scalar slice-element access fails closed). Recursing here would
            // spuriously REJECT that coherent link, not catch a hole (adversarially confirmed inert).
            ty::Ref(_, pointee, rustc_hir::Mutability::Not) => {
                // Trust (B2-3): `ty::Dynamic` joins the Fat set in the same change that
                // flips map_ty's `&dyn` spelling — flipping one without the other reopens
                // the wave-19 DST-coherence hole (an identity-`&T`→concrete-`&dyn` callee
                // link would certify Thin==Thin while the callee record signs fat).
                if matches!(norm(*pointee).kind(), ty::Slice(_) | ty::Str | ty::Dynamic(..)) {
                    FatShape::Fat
                } else {
                    FatShape::Thin
                }
            }
            // Any `&mut _` → THIN `Ty::Ptr` (map_ty:732, incl. `&mut [T]`/`&mut str`).
            ty::Ref(_, _, rustc_hir::Mutability::Mut) => FatShape::Thin,
            // Raw pointer — LOCKSTEP with map_ty's Batch-A arm: slice/str pointee is the
            // FAT `Tuple([Ptr, I64])` pair; array pointee is the same three-way split
            // (concrete length → THIN `Ty::Ptr`, const-generic Param → FAT, anything
            // else fails closed in map_ty → Opaque here). Same no-normalize rationale.
            ty::RawPtr(pointee, _) => match norm(*pointee).kind() {
                ty::Slice(_) | ty::Str => FatShape::Fat,
                ty::Array(_, n) => match (n.try_to_target_usize(tcx), n.kind()) {
                    (Some(_), _) => FatShape::Thin,
                    (None, ty::ConstKind::Param(_)) => FatShape::Fat,
                    (None, _) => FatShape::Opaque,
                },
                ty::Dynamic(..) => FatShape::Opaque,
                _ => FatShape::Thin,
            },
            // Fixed-size array: map_ty needs a CONCRETE length (`try_to_target_usize`), else fails
            // closed (a const-generic `[T; N]`). The element shape carries any nested fatness.
            ty::Array(elem, n) => match n.try_to_target_usize(tcx) {
                Some(_) => agg_or_opaque(vec![self.fat_shape(*elem, visited)]),
                None => FatShape::Opaque,
            },
            ty::Tuple(elems) => {
                agg_or_opaque(elems.iter().map(|e| self.fat_shape(e, visited)).collect())
            }
            // Struct / enum: recurse into field types (map_ty → struct_field_tys/register_enum
            // recurse via map_ty). A recursive adt cycle-guards to Opaque, mirroring map_ty.
            // Batch B LOCKSTEP: `(DefId, args)`-keyed + depth fuel, exactly like
            // `adt_visit_stack` — the DefId-only key silently degraded nested-distinct-
            // instantiation shapes (typenum towers) to Opaque, discarding wave-19 records.
            ty::Adt(adt, adt_args) if adt.is_struct() || adt.is_enum() => {
                if visited.contains(&(adt.did(), *adt_args)) || visited.len() >= ADT_VISIT_FUEL {
                    return FatShape::Opaque;
                }
                visited.push((adt.did(), *adt_args));
                let shape = agg_or_opaque(
                    adt.variants()
                        .iter()
                        .flat_map(|v| v.fields.iter())
                        .map(|f| self.fat_shape(f.ty(tcx, *adt_args).skip_normalization(), visited))
                        .collect(),
                );
                visited.pop();
                shape
            }
            // A fn-pointer TYPE → map_ty lowers it CLEAN as `Ty::Func(sig)` (lib.rs:838), so DON'T
            // leave it to the Opaque catch-all: an inner `fn(&T)`→`fn(&str)` fatness flip must be
            // caught by comparison, not skipped. Recurse into the fn-ptr's own sig positions (the
            // same per-position `map_ty` fatness `map_fn_ptr_ty` uses), independent of whether
            // `splice_ok` later refuses a fn-ptr param — soundness must not rest on that cross-file
            // check.
            ty::FnPtr(..) => {
                let sig = tcx.instantiate_bound_regions_with_erased(ty.fn_sig(tcx));
                agg_or_opaque(
                    sig.inputs_and_output.iter().map(|t| self.fat_shape(t, visited)).collect(),
                )
            }
            // A PATTERN type (`pattern_type!(usize is 0..=N)`) → map_ty widens to the base scalar
            // (lib.rs:845). Mirror that (never fat, but keep it non-Opaque so the skip-Opaque
            // invariant "Opaque ⟺ havoc position" stays exact).
            ty::Pat(base, _) => self.fat_shape(*base, visited),
            // Everything else map_ty fails closed on (or would): bare param, unresolved alias, dyn,
            // foreign, closure/coroutine, never, unions, … → Opaque (conservative).
            _ => FatShape::Opaque,
        }
    }

    /// Admission-faithfulness note (why DefIndex identity stays sound for resolved instances
    /// whose `inst.args` are non-identity, e.g. a generic impl method instantiated concretely):
    /// the ledger links by `DefIndex` to the callee's OWN body record, which was lowered under
    /// IDENTITY args. A generic body only splices if it lowered CLEAN, and every
    /// instantiation-dependent construct — a `ty::Param` in any mapped position, a param-laden
    /// const, a generic-arg call — fails closed with a tag during that body's own lowering. So
    /// any SPLICED body's lowering is instantiation-independent, and linking any concrete
    /// instantiation to it is faithful (the pre-existing convention for generic free fns,
    /// now load-bearing for resolved instances too). Non-spliced callees become bodyless
    /// declarations = havoc, sound for every instantiation.
    fn resolve_callee(
        &mut self,
        mut fun: ExprId,
        from_hir_call: bool,
    ) -> Result<CalleeKind, &'static str> {
        loop {
            match &self.thir.exprs[fun].kind {
                ExprKind::Scope { value, .. } => fun = *value,
                ExprKind::Use { source } => fun = *source,
                _ => break,
            }
        }
        let fun_rty = self.thir.exprs[fun].ty;
        let (def_id, gen_args) = match fun_rty.kind() {
            ty::FnDef(def_id, args) => (*def_id, *args),
            // An indirect call through a first-class fn-pointer value (`let f: fn(i32)->i32
            // = …; f(x)`). The caller lowers the operand and emits `Inst::CallIndirect`.
            ty::FnPtr(..) => return Ok(CalleeKind::FnPtr(fun)),
            // Closure-typed operands never reach here (typeck rewrites `f(x)` on a closure
            // into `Fn*::call*(f, (x,))`, a FnDef); anything else is out of the fragment.
            _ => return Err("Call(indirect non-fn-ptr callee)"),
        };
        // Trust (wave-C): the SITE identity built MIR spells — the THIR callee's `FnDef(def_id, args)`
        // IS what `mir_built` writes (`node_args`, verified `thir/cx/expr.rs`), so this is the exact
        // func-operand identity the shim must reproduce to flip a concrete-mono call. Captured here,
        // BEFORE the resolve path rebinds `gen_args` to the normalized args (`site_args` is the RAW
        // node_args; `site_def_id` is the trait method for a trait/operator call, the free fn / inherent
        // method otherwise). The RESOLVED instance below stays the crate-assembly identity (`FuncId`).
        let site_def_id = def_id;
        let site_args = gen_args;
        // Trust: operator-position failures ("from_hir_call == false" — overloaded operator /
        // index / deref desugars) collapse onto ONE split tag so the ratchet measures the
        // operator bucket separately from explicit method calls.
        let fail = |tag: &'static str| -> &'static str {
            if from_hir_call { tag } else { "Call(operator)" }
        };
        let def_kind = self.tcx.def_kind(def_id);
        // The DIRECT free-fn path (no resolution: a free fn IS its own instance; intrinsics/
        // track_caller stay extern-declared = havoc at assembly).
        //
        // Trust (wave-19 fix): the direct path must ALSO be DST-coherence-gated. A generic free fn
        // `fn id<T:?Sized>(x:&T)->&T` lowers its identity record with `&T`→thin `Ty::Ptr`
        // (map_ty:732); a call `id::<str>(s)` would link the caller's FAT `&str` into that thin slot
        // (adversarially confirmed — this fast path bypassed the earlier admission gate entirely).
        // Admit only if the site's `gen_args` keep every mapped position's `map_ty` fatness in
        // agreement with the identity record; a concrete unsized substitution flips a thin position
        // fat and fails closed, while a generic-caller-forwarded param stays coherent (both sides
        // thin/opaque) and a non-local free fn is havoc → admitted unconditionally.
        if from_hir_call && matches!(def_kind, rustc_hir::def::DefKind::Fn) {
            if self.sig_shapes_coherent(def_id, gen_args) {
                // Trust (wave-C): a free fn IS its own site identity — record `site_args` so a
                // concrete-generic call (`id::<i32>(x)`) can flip; zero-generic stays `[]` (wave-6).
                return Ok(CalleeKind::Direct(self.admit_callee_site(
                    def_id,
                    site_def_id,
                    site_args,
                )));
            }
            return Err(fail("Call(DST-incoherent instantiation)"));
        }
        match def_kind {
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
            rustc_hir::def::DefKind::Ctor(..) => return Err(fail("Call(ctor)")),
            _ => return Err(fail("Call(unsupported callee def-kind)")),
        }
        // Trust: `extern "rust-call"` (`Fn`/`FnMut`/`FnOnce::call*`) UNTUPLES its tupled args at
        // the ABI boundary; emitting a plain `Inst::Call` with the tupled arg would be an arity
        // lie against the callee body's real params. Gate on the UNRESOLVED sig so the closure
        // `f(u, v)` → `call*(f, (u, v))` rewrite is caught before resolution — then hand the
        // whole rust-call family to the dedicated resolver, whose ONE admitted outcome
        // (`CalleeKind::ClosureCall`) makes the call site perform the untupling honestly;
        // every other shape keeps a precise fail-closed tag.
        // Trust: rust 1.99 — `FnSig.abi` is now an accessor method, not a field.
        if fun_rty.fn_sig(self.tcx).skip_binder().abi() == rustc_abi::ExternAbi::RustCall {
            return self.resolve_fn_trait_callee(def_id, gen_args).map_err(fail);
        }
        // A generic CALLER's call site carries unsubstituted params — there is no concrete
        // instance to resolve (`TypingEnv::fully_monomorphized` requires param-free input).
        if gen_args.has_non_region_param() || gen_args.has_non_region_infer() {
            // Trust (wave-20): admit an explicit-CALL generic callee as a FORCED-HAVOC bodyless
            // declaration. The polymorphic target cannot be resolved to a concrete instance here
            // (and MUST NOT link to the callee's identity-lowered body — that DefIndex may hold a
            // clean local body, e.g. a trait default, which would be an identity lie AND re-open
            // the wave-19 fat/thin DST hole at a generic site where `sig_shapes_coherent` is inert).
            // A havoc decl claims no body/ABI, so it is sound at EVERY monomorphization: the emitted
            // `Inst::Call` sets `contains_call` → the differential forces `mode=NotRun` (never a
            // wrong Agreed), and the flip shim rejects a generic callee (`generics_of != 0`) → the
            // body never flips. Returns BEFORE the opaque/resolution queries below, so no E0391
            // cycle risk.
            //
            // Trust (wave-N): the same FORCED-HAVOC admission now also covers OPERATOR-position
            // generic callees (`from_hir_call == false`) — the derived `PartialEq::eq(&self.f,
            // &other.f)` / `Ord::cmp` idiom over a generic FIELD, whose `<T as Trait>::method`
            // carries the field param. The wave-20 `if from_hir_call` restriction was conservative:
            // the only TUPLED operator (closure `()` → rust-call) is already diverted at the
            // `ExternAbi::RustCall` gate above, so every operator desugar reaching here is a PLAIN
            // normal-ABI call whose args lower identically regardless of `from_hir_call`; havoc is
            // sound at operator position for the same no-body/no-ABI reason (→ NotRun, never flips).
            return Ok(CalleeKind::Direct(self.admit_havoc_callee(def_id)));
        }
        // Trust: an OPAQUE type (RPIT / async fn future) in the callee's args or signature —
        // normalizing/resolving it from inside `mir_built` can demand the opaque's hidden
        // type, whose computation needs borrowck of the DEFINING body: an E0391 query cycle
        // when the callee is (mutually) recursive with the body being built (observed on
        // self-recursive RPIT and async fns in tests/ui/impl-trait). Fail closed before
        // touching the queries.
        if gen_args.has_opaque_types() || fun_rty.fn_sig(self.tcx).skip_binder().has_opaque_types()
        {
            // Trust (wave-ER): admit an RPIT/async-sig callee (`drain_all() -> impl
            // Iterator<Item = Line>`) as a FORCED-HAVOC bodyless declaration — the wave-20
            // generic-callee posture — instead of failing closed. NO resolution /
            // normalization / sig mapping happens on this path (`admit_havoc_callee` records
            // DefId + path only), so the E0391 hidden-type query cycle the old fail-closed
            // tag guarded against (demanding the opaque's hidden type can require borrowck
            // of its DEFINING body) is never risked. The emitted `Inst::Call` sets
            // `contains_call` → NotRun; a havoc decl never links a body (`force_havoc` joins
            // the dedup key) and never flips — the call is a plain opaque effect boundary,
            // its args still lowering (or failing) at their own sites.
            return Ok(CalleeKind::Direct(self.admit_havoc_callee(def_id)));
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        // Normalize-then-resolve — the exact `CheckCallRecursion` pattern (aliases in the args
        // block resolution otherwise).
        // Trust: rust 1.99 — `try_normalize_erasing_regions` takes `Unnormalized<T>` (`new_wip`).
        let Ok(gen_args) =
            self.tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(gen_args))
        else {
            return Err(fail("Call(generic callee)"));
        };
        match ty::Instance::try_resolve(self.tcx, typing_env, def_id, gen_args) {
            Ok(Some(inst)) => match inst.def {
                ty::InstanceKind::Item(resolved) => {
                    if self.tcx.is_closure_like(resolved) {
                        // A NON-rust-call sig resolving to a closure-like body (the
                        // `Fn*::call*` path is handled by `resolve_fn_trait_callee` above):
                        // defensive — its (env, declared…) convention is not this call's
                        // shape, never link it.
                        Err(fail("Call(closure call)"))
                    } else if !self.sig_shapes_coherent(resolved, inst.args) {
                        // Trust (wave-19): the concrete monomorphized signature is ABI-INCOHERENT
                        // with the callee's IDENTITY-lowered crate-module record. `map_ty` signs a
                        // `&T` whose (normalized) pointee is not a concrete slice/str (incl. `&Self`,
                        // `&Param`, `&Self::Assoc`) as a THIN `Ty::Ptr`, so the record's slot is thin;
                        // a monomorphization that turns that position — top-level, behind a
                        // projection, OR nested in a tuple/array/struct/enum — into a FAT `&str`/`&[T]`
                        // reference would have the caller pass a fat `(ptr,len)` tuple into (or read a
                        // fat return from) that thin slot, dropping the length lane (adversarially
                        // confirmed: the top-level `fn get(s:&str)->&str{ s.me() }` over
                        // `trait Id{ fn me(&self)->&Self{self} } impl Id for str{}`, AND the NESTED
                        // `(&U,i32)`→`(&str,i32)` / `Wrap<T>`→`Wrap<str>` forms). Fail closed.
                        // Coherent instantiations still admit — this gates the wave-19 trait-DEFAULT
                        // surface AND the pre-existing generic free-fn / impl-method admission
                        // (same root: map_ty collapses `&Param` to thin).
                        Err(fail("Call(DST-incoherent instantiation)"))
                    } else {
                        // Admit the resolved instance — including a trait DEFAULT body. Faithful by
                        // the splice-only-if-clean convention (admission-faithfulness note above):
                        // a spliced generic/default body is instantiation-INDEPENDENT (every
                        // instantiation-dependent construct fails closed during its own lowering);
                        // linking any concrete monomorphization to its identity-lowered (DefIndex)
                        // record is sound now that `sig_shapes_coherent` has ruled out the fat/thin
                        // DST-reference exception at every nesting depth. Links to the site-spelled
                        // DefId — ZERO normalizations of the callee identity. A non-clean default
                        // becomes a bodyless havoc declaration.
                        //
                        // Trust (wave-C): `resolved` stays the crate-assembly identity (`FuncId`/dedup
                        // — no `crate_module` regression), while `site_def_id`/`site_args` carry what
                        // built MIR spells (the TRAIT method + Self for a trait/operator call). The shim
                        // spells `FnDef(site_def_id, site_args)` and fails closed if the args are not
                        // in the encodable concrete fragment → the body stays clean-only. The wave-19
                        // `sig_shapes_coherent` gate above is untouched.
                        Ok(CalleeKind::Direct(self.admit_callee_site(
                            resolved,
                            site_def_id,
                            site_args,
                        )))
                    }
                }
                // Trust (B2-3 slice 2): dyn DISPATCH routes into the wave-20 FORCED-HAVOC
                // bodyless-decl lane. The callee a vtable call runs is unknowable at
                // compile time, so the ONLY sound record is `admit_havoc_callee` —
                // `force_havoc` joins the ledger dedup key and the crate assembler's
                // force_havoc arm DECLARES (never links), even when the trait method's
                // own DefIndex owns a clean local DEFAULT body (linking it would be the
                // identity lie: runtime dispatch may select an overriding impl). The
                // never-flip invariant is structural: a havoc admit has `site=None` ⇒
                // `site_args=None`, so the to_mir shim fail-closes the Call (plus the
                // explicit force_havoc reject there); a derived DIRECT call in built
                // MIR's vtable-dispatch position would be a miscompile. The routed body
                // lowers CLEAN and the seam's declaration gate classes it
                // clean-skip-extern-callee (coverage-only) — never interpreted, never
                // flipped, never counted verified. The `vdef == def_id` tripwire keeps
                // any resolution REDIRECT (a Virtual instance whose def differs from the
                // site-spelled trait method) fail-closed: the ledger records the SITE
                // def_id, and a silent redirect would change the assembly identity.
                ty::InstanceKind::Virtual(vdef, _) => {
                    if vdef != def_id {
                        return Err(fail("Call(dyn dispatch)"));
                    }
                    Ok(CalleeKind::Direct(self.admit_havoc_callee(def_id)))
                }
                ty::InstanceKind::Intrinsic(..) => Err(fail("Call(intrinsic)")),
                _ => Err(fail("Call(instance shim)")),
            },
            // Trust (wave-20): resolution could not select a concrete instance even with param-free
            // args (a still-polymorphic target). Same FORCED-HAVOC posture as the generic gate above
            // — a bodyless decl, sound at every mono. Trust (wave-N): operator desugars included too
            // (the RustCall untupling family is already diverted above → this is a plain call).
            Ok(None) => Ok(CalleeKind::Direct(self.admit_havoc_callee(def_id))),
            Err(_guar) => Err(fail("Call(resolution error)")),
        }
    }

    /// Trust: resolve a rust-call-ABI callee (`Fn`/`FnMut`/`FnOnce::call*` after the
    /// `resolve_callee` ABI gate). ONE outcome is admitted — `CalleeKind::ClosureCall` — and it
    /// is PROVEN, not assumed, step by step:
    ///
    ///   * the callee must be an assoc fn of one of the built-in `Fn`/`FnMut`/`FnOnce` traits
    ///     (`fn_trait_kind_from_def_id`), so `gen_args` is exactly `[Self, Args]` and
    ///     `type_at(0)` is the receiver type (any other rust-call def — e.g. a user-written
    ///     `extern "rust-call" fn` under `unboxed_closures` — stays "Call(rust-call ABI)");
    ///   * the same generic/opaque/normalization guards as the main `resolve_callee` path
    ///     (identical tags for identical reasons: an `F: Fn(…)` bound's call is a generic
    ///     callee; an RPIT-returned closure's opaque `Self` risks the E0391 query cycle);
    ///   * the receiver must be a PLAIN `ty::Closure` — then `Instance::try_resolve` runs the
    ///     very same `resolve_closure` logic codegen uses: `InstanceKind::Item(closure)` is
    ///     returned exactly when no adapter shim is needed ((actual, requested) kind in
    ///     {(Fn,Fn),(Fn,FnMut),(FnMut,FnMut),(FnOnce,FnOnce)}); a `Fn`/`FnMut` closure invoked
    ///     via `call_once` surfaces as `ClosureOnceShim` → "Call(instance shim)";
    ///   * the resolved Item must be that same LOCAL, non-coroutine closure (tripwires —
    ///     "Call(closure call)"), with an EMPTY capture list and a by-ref env:
    ///       - `upvar_tys()` non-empty ⇒ the env value at the call site must alias the real
    ///         capture frame, which closure construction does not lower yet — fail closed
    ///         "Call(closure env unsupported)";
    ///       - kind `Fn`/`FnMut` + no captures ⇒ the closure BODY's wave-1 signing is
    ///         `(env: Ty::Ptr, declared…)` (`closure_env_param_ty`: `closure_env_ty` gives
    ///         `&{closure}` / `&mut {closure}` — a thin ref → `Ty::Ptr`), and since the capture
    ///         list is empty NO upvar projection can exist in the body, so a fresh unit-slot
    ///         pointer is indistinguishable (within the fragment) from a pointer to the real
    ///         (zero-sized) closure place — the call site builds exactly that;
    ///       - kind `FnOnce` (by-value env) with no captures cannot be inferred (kind inference
    ///         yields `Fn` for capture-free closures) — kept fail-closed as a tripwire.
    ///
    /// The returned `FuncId` is ledgered via `admit_callee` under the closure body's DefIndex:
    /// closure bodies run through the same `mir_built` hook → `crate_module::record` as any
    /// body, so crate-level assembly splices the edge when the closure body lowered clean and
    /// havocs (bodyless declaration) otherwise.
    fn resolve_fn_trait_callee(
        &mut self,
        def_id: DefId,
        gen_args: ty::GenericArgsRef<'tcx>,
    ) -> Result<CalleeKind, &'static str> {
        // Only the built-in Fn-trait methods are modeled; other rust-call defs stay residual.
        let is_fn_trait_method = self
            .tcx
            .trait_of_assoc(def_id)
            .and_then(|tr| self.tcx.fn_trait_kind_from_def_id(tr))
            .is_some();
        if !is_fn_trait_method {
            return Err("Call(rust-call ABI)");
        }
        // A generic CALLER's call site (`F: Fn(…)` bound) — no concrete instance to resolve.
        if gen_args.has_non_region_param() || gen_args.has_non_region_infer() {
            return Err("Call(generic callee)");
        }
        // Same E0391 query-cycle guard as the main path (e.g. calling an RPIT-returned
        // closure: `Self` is the defining fn's opaque type).
        if gen_args.has_opaque_types() {
            return Err("Call(opaque type in callee sig)");
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        // Trust: rust 1.99 — `try_normalize_erasing_regions` takes `Unnormalized<T>` (`new_wip`).
        let Ok(gen_args) =
            self.tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(gen_args))
        else {
            return Err("Call(generic callee)");
        };
        // Receiver (Self) shape: only a PLAIN closure proceeds to resolution. `dyn Fn*` gets
        // its precise existing tag; fn-def/fn-ptr receivers (FnPtrShim) and coroutine-closures
        // (their own shim family) stay in the residual rust-call bucket.
        let ty::Closure(closure_def_id, closure_args) = *gen_args.type_at(0).kind() else {
            return Err(match gen_args.type_at(0).kind() {
                ty::Dynamic(..) => "Call(dyn dispatch)",
                _ => "Call(rust-call ABI)",
            });
        };
        match ty::Instance::try_resolve(self.tcx, typing_env, def_id, gen_args) {
            Ok(Some(inst)) => match inst.def {
                ty::InstanceKind::Item(resolved) => {
                    // Tripwires: resolution must land on the receiver closure itself, local
                    // and non-coroutine — anything else is a closure body we must not link.
                    if resolved != closure_def_id
                        || !resolved.is_local()
                        || self.tcx.is_coroutine(resolved)
                    {
                        return Err("Call(closure call)");
                    }
                    // Trust (wave-CF): a CAPTURING Fn/FnMut closure is now admitted. `capturing`
                    // selects, at the ClosureCall Call arm, the REAL-env path (materialize the
                    // `Ty::Tuple(captures)` value the `ExprKind::Closure` value arm bound to the
                    // closure local and pass its address) over the wave-5 fresh-unit-slot path.
                    // If the env could NOT be materialized (a non-thin/Drop capture → the closure
                    // local never lowered clean), the Call arm's `local_value`/`Ty::Tuple` gate
                    // fails closed. A capture-free closure keeps `capturing == false`.
                    let capturing = !closure_args.as_closure().upvar_tys().is_empty();
                    match closure_args.as_closure().kind() {
                        // By-ref env (`&{closure}`/`&mut {closure}`): non-capturing rebuilds a
                        // fresh unit-slot Ptr (see the doc above); capturing passes the address of
                        // the real env tuple.
                        ty::ClosureKind::Fn | ty::ClosureKind::FnMut => {
                            Ok(CalleeKind::ClosureCall {
                                callee: self.admit_callee(resolved),
                                capturing,
                            })
                        }
                        // By-value env (`FnOnce`): a different ABI (env passed by value, not by
                        // ref) — not modeled; fail closed. (For a capture-free closure kind
                        // inference yields `Fn`, so this is the genuinely by-value case.)
                        ty::ClosureKind::FnOnce => Err("Call(closure env unsupported)"),
                    }
                }
                ty::InstanceKind::Virtual(..) => Err("Call(dyn dispatch)"),
                ty::InstanceKind::Intrinsic(..) => Err("Call(intrinsic)"),
                // ClosureOnceShim (`call_once` on a `Fn`/`FnMut` closure), FnPtrShim, … —
                // synthetic MIR we do not model.
                _ => Err("Call(instance shim)"),
            },
            Ok(None) => Err("Call(generic callee)"),
            Err(_guar) => Err("Call(resolution error)"),
        }
    }

    /// Trust: is the DISCARDED `Fn*::call*` receiver expr PROVEN effect-free? The supported
    /// `ClosureCall` lowering rebuilds the env param as a fresh unit-slot pointer instead of
    /// lowering the receiver (a borrow of a zero-sized closure place — see
    /// `resolve_fn_trait_callee`), which is only faithful if evaluating the receiver could not
    /// have had observable effects. Allow-list peel: `Scope`/`Use` wrappers, effect-free
    /// `Borrow`s, and BUILT-IN derefs of `ty::Ref` operands (THIR has already desugared
    /// overloaded `Deref` into method calls, and a `&T` read cannot fault), bottoming out at a
    /// pure place read (`VarRef`/`UpvarRef`) or a capture-FREE closure literal (constructing a
    /// zero-sized env evaluates nothing). Anything else — blocks, calls, capturing literals —
    /// returns false and the call fails closed ("Call(closure env unsupported)").
    fn effect_free_closure_receiver(&self, mut e: ExprId) -> bool {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Borrow { arg, .. } => e = *arg,
                ExprKind::Deref { arg }
                    if matches!(self.thir.exprs[*arg].ty.kind(), ty::Ref(..)) =>
                {
                    e = *arg
                }
                ExprKind::VarRef { .. } | ExprKind::UpvarRef { .. } => return true,
                ExprKind::Closure(closure) => return closure.upvars.is_empty(),
                _ => return false,
            }
        }
    }

    /// Trust (wave-CF): materialize a CAPTURING closure's env for a `ClosureCall`. The receiver
    /// `recv` is `&f` — the closure LOCAL `f` holds the env `Ty::Tuple(captures)` VALUE that the
    /// `ExprKind::Closure` value arm built and `set_local` bound. Peel `Scope`/`Use`/`Borrow` to
    /// the local, read its bound value + declared type (`map_ty(closure) = Ty::Tuple`), `Alloca` a
    /// fresh slot, `Store` the env into it, and return the slot ptr — the closure BODY (wave-CE)
    /// `Load`s `Ty::Tuple(captures)` through it. FAIL CLOSED ("Call(closure env unsupported)") if
    /// the receiver is not a bound local closure (an IIFE `(||…)()`, a closure-typed param, a
    /// nested-closure upvar) or the local is unbound / not a `Ty::Tuple` (a non-thin/Drop capture
    /// left the closure local unlowered). CLEAN-ONLY: the non-scalar `Alloca{Ty::Tuple}`/`Store`
    /// fails closed in the shim (`to_mir` "Alloca of non-scalar pointee"), so the enclosing body —
    /// itself `NotRun` because it contains this call — never flips.
    fn materialize_closure_env(&mut self, span: rustc_span::Span, recv: ExprId) -> Option<ValueId> {
        let mut e = recv;
        let local = loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Borrow { arg, .. } => e = *arg,
                ExprKind::VarRef { id } => break Some(*id),
                _ => break None,
            }
        };
        let Some(local) = local else {
            self.unsupported.push((format!("{span:?}"), "Call(closure env unsupported)"));
            return None;
        };
        let (Some(env_val), Some(env_ty)) = (self.local_value(local), self.local_ty(local)) else {
            self.unsupported.push((format!("{span:?}"), "Call(closure env unsupported)"));
            return None;
        };
        if !matches!(env_ty, Ty::Tuple(_)) {
            self.unsupported.push((format!("{span:?}"), "Call(closure env unsupported)"));
            return None;
        }
        let slot = self.fresh();
        self.push_node(InstrNode::new(Inst::Alloca { ty: env_ty.clone(), count: None, align: None })
                .with_result(slot),
        );
        self.push_node(InstrNode::new(Inst::Store {
            ty: env_ty,
            ptr: slot,
            value: env_val,
            volatile: false,
            align: None,
        }));
        Some(slot)
    }

    /// Trust: is `e` (peeled) a PLAIN, NON-capturing closure literal? Gates the `let`-binding
    /// skip in `lower_stmt` (see the comment there). Three checks, all required:
    ///   * `ExprKind::Closure` whose `args` are `ty::UpvarArgs::Closure` — coroutines and
    ///     coroutine-closures (`async`/`gen` blocks) use their own `UpvarArgs` variants and are
    ///     NOT effect-free-by-construction claims we make;
    ///   * an EMPTY `upvars` list — no capture operands exist, so constructing the value
    ///     evaluates nothing;
    ///   * the expr's type is `ty::Closure` (belt-and-braces against a shape drift).
    fn non_capturing_closure_literal(&self, mut e: ExprId) -> bool {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Closure(c) => {
                    return matches!(c.args, ty::UpvarArgs::Closure(_))
                        && c.upvars.is_empty()
                        && matches!(self.thir.exprs[e].ty.kind(), ty::Closure(..));
                }
                _ => return false,
            }
        }
    }

    /// Trust (wave-22): is `e` (after peeling `Scope`/`Use`) ANY closure/coroutine LITERAL — a plain
    /// closure `|…| {…}`, a capturing `move |…| {…}`, an `async {…}`/`async |…| {…}` block, or a
    /// `#[coroutine] || {…}` (any `UpvarArgs`, any capture list)? Unlike `non_capturing_closure_literal`
    /// this does NOT require the capture list to be empty or the args to be a plain closure — it is used
    /// ONLY at DISCARD positions (a bare expression statement, or a `let _ =` wildcard binding) where the
    /// constructed value is immediately dropped and never called/polled, so capture-count/coroutine-ness
    /// is irrelevant to faithfulness. A CALLED closure `(|| …)()` peels to `ExprKind::Call`, not
    /// `Closure`, so it is never matched here.
    fn closure_literal(&self, mut e: ExprId) -> bool {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Closure(_) => return true,
                _ => return false,
            }
        }
    }

    /// Trust: produce the UNTUPLED argument values for a `ClosureCall` from the rust-call
    /// tupled-args operand (THIR arg 1). Two proven shapes, everything else fail-closed:
    ///
    ///   * a literal `ExprKind::Tuple` (the `f(u, v)` → `call*(f, (u, v))` desugar synthesizes
    ///     exactly this — `rustc_mir_build::thir::cx::expr`): lower each field expr directly,
    ///     NEVER materializing the tuple — the same per-element evaluation order MIR gives the
    ///     tuple temp's fields, and `lower_call_args` keeps the existing borrow-ptr argument
    ///     admissions + the "Call(unsupported arg)" fail-closed contract. The zero-arg call
    ///     `f()` is the empty literal tuple → zero values.
    ///   * a NON-literal tuple operand (UFCS `Fn::call(&f, t)`): lower the tuple VALUE and
    ///     `ExtractField` each element — restricted to scalar element types, the same
    ///     restriction as the `ExprKind::Field` arm (the producer's `Ty::Tuple` aggregates
    ///     carry scalar fields; a wider claim would be unproven). Any gap — unmappable tuple
    ///     type, non-scalar element, unloweable operand, a borrow-ptr-typed aggregate — fails
    ///     closed as "Call(closure untuple unsupported)".
    fn lower_closure_call_untupled(
        &mut self,
        expr_span: rustc_span::Span,
        mut tup: ExprId,
    ) -> Option<Vec<ValueId>> {
        loop {
            match &self.thir.exprs[tup].kind {
                ExprKind::Scope { value, .. } => tup = *value,
                ExprKind::Use { source } => tup = *source,
                _ => break,
            }
        }
        if let ExprKind::Tuple { fields } = &self.thir.exprs[tup].kind {
            let field_ids: Vec<ExprId> = fields.iter().copied().collect();
            // Untupled closure args are never diverging-dropped (the diverging-arg-skip is a
            // direct/indirect-call concern; keep closure calls fail-closed on an unloweable arg).
            return self.lower_call_args(expr_span, &field_ids, false, false, false);
        }
        let fail = |cx: &mut Self| {
            cx.unsupported.push((format!("{expr_span:?}"), "Call(closure untuple unsupported)"));
            None
        };
        let tup_rty = self.thir.exprs[tup].ty;
        let ty::Tuple(elem_tys) = tup_rty.kind() else {
            return fail(self);
        };
        // The empty non-literal tuple is a UNIT operand — `lower_expr` has no value for it
        // (and `None` would be ambiguous with a fail-closed lowering), so only the literal
        // path above supports zero-arg calls.
        if elem_tys.is_empty() {
            return fail(self);
        }
        let Some(Ty::Tuple(field_tys)) = self.map_ty_checked(tup_rty) else {
            return fail(self);
        };
        if field_tys.len() != elem_tys.len() {
            return fail(self);
        }
        // Scalar-element restriction — exactly the `ExprKind::Field` arm's proven
        // `ExtractField` fragment.
        if !field_tys.iter().all(|t| {
            matches!(
                t,
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
                    | Ty::F32
                    | Ty::F64
            )
        }) {
            return fail(self);
        }
        let Some(agg) = self.lower_expr(tup) else {
            return fail(self);
        };
        if self.is_borrow_ptr(agg) {
            return fail(self);
        }
        let mut vals = Vec::with_capacity(field_tys.len());
        for (i, fty) in field_tys.iter().enumerate() {
            let v = self.fresh();
            self.push_node(InstrNode::new(Inst::ExtractField {
                    ty: fty.clone(),
                    aggregate: agg,
                    field: i as u32,
                })
                .with_result(v),
            );
            vals.push(v);
        }
        Some(vals)
    }

    /// Trust: lower every call argument, fail-closed as a unit (never emit a call with a hole).
    /// Borrow-produced pointers ARE admitted as arguments — this is PROVEN faithful within the
    /// producer's fragment, not assumed:
    ///
    ///   * a `&mut` arg is the PROMOTED local's slot `Ptr` (`ExprKind::Borrow{Mut}` arm): the
    ///     slot is that local's single source of truth for its whole lifetime (every caller
    ///     read/write is a `Load`/`Store` on it), so a spliced callee's stores through the
    ///     pointer are exactly the writes the memory model already expects to be visible, and
    ///     an extern/unlowered callee is a bodyless declaration whose consumers must havoc
    ///     reachable memory (the fail-closed contract of declarations).
    ///   * a shared `&` arg is a fresh scalar-pointee `Alloca` snapshot of the local's current
    ///     SSA value (`ExprKind::Borrow{Shared}` arm). The Borrow arm only produces SCALAR
    ///     pointees (mapped `Ty::Bool`/ints), and by `map_ty` those come solely from rustc
    ///     `bool`/int/`usize`-family primitives — all `Freeze`, so no UB-free callee can write
    ///     through the pointer and the snapshot equals the place for the whole call. Snapshot
    ///     ADDRESS identity (two `&x` args → two allocas) is unobservable inside the fragment:
    ///     pointer comparisons/casts fail closed in both caller and any spliceable callee, and
    ///     extern callees havoc.
    ///   * (wave-5) a FORWARDED ref-typed param (`g(r)` inside `fn f(r: &T)` — the reborrow
    ///     peel yields the param's own ledger-registered Ptr): the argument IS the caller-of-f's
    ///     pointer, so passing it on is faithful by identity — no snapshot, no new aliasing
    ///     introduced beyond what the incoming reference already carried.
    ///
    /// Anything an argument expression cannot lower stays fail-closed via its OWN precise tag
    /// plus the aggregating "Call(unsupported arg)" marker on the call.
    /// Trust (method-call receiver — temporal write-side, wave-MC): a
    /// `&mut/& (*p).f1.f2.…` METHOD-RECEIVER borrow has no address in the
    /// value-aggregate memory model — `reborrow_target` bottoms out at a `Field`
    /// (`NotAPlace`), so the general `Borrow` arm fails closed
    /// (`Borrow(&mut non-local place)`). But the callee that consumes it (a mutator
    /// like `LazyBuffer::clear` / `Store::clear` / `LazyBuffer::drain_all`) sets
    /// `contains_call`, making this body structurally `NotRun` — never interpreted,
    /// never flipped (CLEAN-ONLY) — so the receiver need not be a real pointer. It
    /// only needs to CARRY the receiver PLACE-PATH into the emitted IR, so a
    /// downstream temporal extractor can resolve the callee in its method-effect KB
    /// and project the effect (`LazyBuffer::clear` → the `retained` field = 0). We
    /// lower the receiver's INNER PLACE as a VALUE — `Load` the root struct +
    /// `ExtractField`-chain to the leaf, via the SAME opaque-tolerant read
    /// machinery the `self.storage.<field>` nested read uses — which is exactly the
    /// place-path carrier. Recognized ONLY for a nested FIELD place
    /// (`field_chain_deref_place` succeeds) whose leaf lowers cleanly; a bare local
    /// (`&x`), raw-ptr deref, or non-value-lowerable leaf keeps the caller's tag.
    fn try_lower_receiver_place_value(&mut self, a: ExprId) -> Option<ValueId> {
        let mut e = a;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                _ => break,
            }
        }
        let place = match &self.thir.exprs[e].kind {
            ExprKind::Borrow { arg, .. } => *arg,
            _ => return None,
        };
        // A NESTED field place (`(*p).f…`) — the method-receiver shape — lowers as its leaf field
        // VALUE (the read machinery emits `Load` of the root struct + the `ExtractField` chain to
        // the leaf). Fails closed if the leaf is not value-lowerable (a raw ptr, …).
        if self.field_chain_deref_place(place).is_some() {
            return self.lower_expr(place);
        }
        // Trust (realbody store move-out): a `&mut <bare local>` receiver — the real
        // `let mut store = reflowed.store; let _ = store.clear();` shape. `store` is a non-scalar
        // OPAQUE aggregate that `lower_stmt` bound as an SSA value (promotion to a scalar slot was
        // declined — a `Store { lines: Vec, .. }` has no faithful scalar-slot model), so `&mut store`
        // has no slot pointer and the general `Borrow` arm declined above. Carry the local's current
        // VALUE as the receiver place-path — the callee (`Store::clear`) is an opaque `call @callee`
        // that sets `contains_call` → the body is structurally NotRun (never interpreted/flipped), so
        // the receiver need not be a real pointer. Gated to a bound, NON-slot-backed local: a scalar
        // `&mut x` local IS slot-promoted (so its `&mut` lowered via the `Borrow` arm and never
        // reached this fallback), and a real `&mut store` ARG (non-receiver) still declines at its
        // own `Borrow` site.
        let tgt = match self.reborrow_target(place, true) {
            ReborrowTarget::Local(v) => Some(v),
            _ => match self.reborrow_target(place, false) {
                ReborrowTarget::Local(v) => Some(v),
                _ => None,
            },
        };
        if let Some(var) = tgt {
            if self.promoted_slot(var).is_none() {
                if let Some(v) = self.local_value(var) {
                    // Trust (B3-2c seam guard): a VALUE carried where the callee
                    // expects a pointer — CLEAN-ONLY; the seam must not interpret.
                    self.place_path_carrier = true;
                    if !self.is_borrow_ptr(v) {
                        return Some(v);
                    }
                }
            }
        }
        // Trust (wave-ER): a `&mut *p` / `&*p` receiver where `p` is an OPAQUE-CARRIER local —
        // a let-chain payload binding over an opaque enum (`if let Some(sb) = …as_mut()` …
        // `sb.clear()`). The reborrow peel bottoms at `Ptr(VarRef(p))`; carry `p`'s bound
        // opaque value as the receiver — the same NotRun opaque-call posture as the bare-local
        // arm above. Writes the callee performs through this receiver land INSIDE the opaque
        // lane's PAYLOAD, which the type model already treats as one indivisible opaque unit
        // (the lane is non-scalar, hence never projected) — so no projected effect can hide
        // behind the carrier. Gated STRICTLY to `opaque_carrier_locals` (provenance: this
        // wave's own bindings), never an arbitrary ref-typed local.
        let ptr_tgt = match self.reborrow_target(place, true) {
            ReborrowTarget::Ptr(inner) => Some(inner),
            _ => match self.reborrow_target(place, false) {
                ReborrowTarget::Ptr(inner) => Some(inner),
                _ => None,
            },
        };
        if let Some(inner) = ptr_tgt {
            if let Some(var) = self.place_local(inner) {
                if self.opaque_carrier_locals.contains(&var) && self.promoted_slot(var).is_none() {
                    if let Some(v) = self.local_value(var) {
                        if !self.is_borrow_ptr(v) {
                            return Some(v);
                        }
                    }
                }
            }
        }
        None
    }

    /// Trust (wave-RS, `TRUST_SHARED_RECV_PLACE=1`): a SHARED borrow `&x.field-chain` in
    /// explicit-call-arg position whose LEAF is a registered NON-scalar lane lowers as the leaf
    /// field VALUE — the same place-path carrier the wave-MC `&mut` receiver lane emits — so the
    /// callee (`len()`, `is_empty()`, …) becomes ATTRIBUTABLE to the place instead of receiving
    /// the raw base pointer / a byte-offset `gep` (see `shared_recv_place_enabled` for the
    /// measured eventlog-real gap + the soundness argument). `None` (caller keeps the pre-wave
    /// lowering, byte-identical) when: the flag is off, the arg is not a shared borrow of a
    /// resolvable field-chain place, the leaf's REGISTERED lane is a scalar/pointer (its pointee
    /// bytes are semantically load-bearing — the faithful pointer/snapshot lowerings keep it), or
    /// the leaf value does not lower cleanly (tags rolled back — the normal path re-lowers and
    /// keeps its precise tags).
    fn try_lower_shared_recv_place(&mut self, a: ExprId) -> Option<ValueId> {
        if !shared_recv_place_enabled() {
            return None;
        }
        let mut e = a;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                _ => break,
            }
        }
        let ExprKind::Borrow { borrow_kind, arg } = &self.thir.exprs[e].kind else {
            return None;
        };
        if !matches!(
            borrow_kind,
            rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_)
        ) {
            return None;
        }
        let place = *arg;
        let mark = self.unsupported.len();
        let (_, deref_expr, chain) = self.field_chain_deref_place(place)?;
        // Walk the REGISTERED lane types down the chain (the deterministic opaque-tolerant
        // build — the same table the read/write sides use), and require a NON-scalar leaf.
        let pointee_rty = self.thir.exprs[deref_expr].ty;
        let (adt, gargs) = match pointee_rty.kind() {
            ty::Adt(adt, gargs) if adt.is_struct() => (*adt, *gargs),
            _ => return None,
        };
        let Some(mut lane_ty) = self.struct_ty_rmw_opaque(adt, gargs, None) else {
            self.unsupported.truncate(mark);
            return None;
        };
        for (_, idx) in &chain {
            let Ty::Struct(sid) = lane_ty else {
                self.unsupported.truncate(mark);
                return None;
            };
            let Some(ft) = self
                .registered_struct_field_tys(sid)
                .and_then(|fts| fts.get(*idx as usize).cloned())
            else {
                self.unsupported.truncate(mark);
                return None;
            };
            lane_ty = ft;
        }
        // Scalars (incl. floats) and pointers keep their faithful pointer/snapshot
        // lowerings — only container/opaque aggregate lanes ride the place carrier.
        if is_scalar_ty(&lane_ty) || matches!(lane_ty, Ty::Ptr | Ty::F32 | Ty::F64) {
            return None;
        }
        match self.lower_expr(place) {
            Some(v) if !self.is_borrow_ptr(v) => {
                // Trust (B3-2c seam guard): value-instead-of-pointer receiver.
                self.place_path_carrier = true;
                Some(v)
            }
            _ => {
                self.unsupported.truncate(mark);
                None
            }
        }
    }

    /// Trust (realbody, opaque-lane Option READ): read a `(*p).f…scrollback` place whose LEAF is a
    /// provably-OPAQUE `Option<T>` lane — a field `struct_ty_rmw_opaque` collapsed to a `Ty::Unit`
    /// placeholder because its payload `T` is non-pure-value (a `Vec`/`Store`/data-enum, so
    /// `fat_shape(Option<T>) == Opaque`). Returns the leaf's OPAQUE `Ty::Unit` value (Load root +
    /// `ExtractField` chain), used as the receiver of an opaque `Option::{is_some,is_none}` call.
    ///
    /// SOUNDNESS (fail-closed): fires ONLY when the leaf is (a) reached via a NESTED FIELD place
    /// (`field_chain_deref_place` — a struct-field lane, never a bare local Option), (b) the `Option`
    /// lang enum, and (c) `fat_shape == Opaque`. A real `Option<scalar>` has `fat_shape ==
    /// Agg([Scalar])` (pure value) — NOT `Opaque` — so it is REFUSED here and keeps declining, exactly
    /// as required (a projected scalar Option must never silently opaque).
    ///
    /// Trust (wave-RS, the OPTFLAG READ SIDE): under `TRUST_OPTION_FLAG_LANES=1` the SAME lane
    /// registers as a `Ty::Bool` DISCRIMINANT tag (see `struct_ty_rmw_opaque`), and the pre-wave
    /// `Ty::Unit`-only gate made every read of it decline — the measured flag-ON regression
    /// (is_none/is_some/as_mut on a bool lane refused). The lane check now admits EXACTLY the two
    /// registered shapes — `Ty::Unit` (flag off: the opaque unit read, byte-identical) or `Ty::Bool`
    /// under the flag (the DISCRIMINANT read: a REAL guard value — literal `Some`/`None` stores are
    /// the only writers the producer admits, so the bool faithfully tracks the discriminant) — and
    /// the returned lane type lets the caller pick the read surface. Any other registered lane type
    /// keeps declining (a projected/differently-registered lane never silently rides this channel).
    fn read_opaque_option_lane(&mut self, place: ExprId) -> Option<(ValueId, Ty)> {
        // Must be a nested field place (a struct-field lane), not a bare local / index / deref.
        self.field_chain_deref_place(place)?;
        // Peel to the leaf `Field { lhs, name }`.
        let mut e = place;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                _ => break,
            }
        }
        let (lhs, field_idx) = match &self.thir.exprs[e].kind {
            ExprKind::Field { lhs, name, .. } => (*lhs, name.as_u32()),
            _ => return None,
        };
        // The leaf must be a PROVABLY-OPAQUE Option lane: the `Option` lang enum whose payload `T` is
        // NON-pure-value (`!is_pure_value_shape(fat_shape(Option<T>))` — e.g. `Option<Store>` where
        // `Store` carries a `Vec` → a thin ptr → not pure). That is the EXACT condition under which
        // `struct_ty_rmw_opaque` puts a `Ty::Unit` placeholder at this lane. A pure-value
        // `Option<scalar>` (`fat_shape == Agg([Scalar])`, pure) is refused → keeps declining, as
        // required (a projected scalar Option must never silently opaque).
        let leaf_rty = self.thir.exprs[e].ty;
        let is_option = matches!(leaf_rty.kind(), ty::Adt(adt, _)
            if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(adt.did()));
        if !is_option || is_pure_value_shape(&self.fat_shape(leaf_rty, &mut Vec::new())) {
            return None;
        }
        // Prove the HOLDER struct actually places an admissible lane at this leaf index (so the
        // `ExtractField` below is well-typed and the lane genuinely round-trips untouched). This is
        // the "a field `struct_ty_rmw_opaque` collapsed to `Ty::Unit` (or, under the flag, registered
        // as the `Ty::Bool` discriminant)" proof, exact — belt-and-braces over the `!is_pure_value`
        // check (which would also reject a pure `Option<scalar>` that merely failed to `map_ty`).
        let holder_rty = self.thir.exprs[lhs].ty;
        let lane_ty = match holder_rty.kind() {
            ty::Adt(hadt, hargs) if hadt.is_struct() => self
                .struct_ty_rmw_opaque(*hadt, *hargs, None)
                .and_then(|t| match t {
                    Ty::Struct(sid) => self.registered_struct_field_tys(sid),
                    _ => None,
                })
                .and_then(|fts| fts.get(field_idx as usize).cloned())
                .filter(|ft| match ft {
                    Ty::Unit => true,
                    // The wave-RS bool DISCRIMINANT lane — only ever registered under the flag
                    // (mirror the registration arm exactly, never trust `Ty::Bool` alone).
                    Ty::Bool => option_flag_lanes_enabled(),
                    _ => false,
                }),
            _ => None,
        };
        let lane_ty = lane_ty?;
        // Read the holder aggregate (the nested `self.storage` read via the opaque-tolerant builder),
        // then `ExtractField` the lane (the opaque `Ty::Unit` unit, or the `Ty::Bool` discriminant).
        let holder = self.lower_expr(lhs)?;
        let recv = self.fresh();
        self.push_node(InstrNode::new(Inst::ExtractField {
                ty: lane_ty.clone(),
                aggregate: holder,
                field: field_idx,
            })
            .with_result(recv),
        );
        Some((recv, lane_ty))
    }

    /// Trust (realbody, opaque-lane Option READ surface): recognize `<recv>.is_some()` /
    /// `<recv>.is_none()` invoked on a PROVABLY-OPAQUE `Option<T>` field lane and lower the result as
    /// an OPAQUE bool — an opaque `call @Option::{is_some,is_none}` whose receiver is the opaque
    /// `Ty::Unit` lane value (`read_opaque_option_lane`). The call sets `contains_call` (the body is
    /// structurally NotRun — never interpreted/flipped), and the resulting bool feeds the enclosing
    /// `if` / `&&` as an OPAQUE condition (the extractor's opaque-branch collapse handles it, failing
    /// closed if the arms disagree on projected effects). Returns the bool `ValueId` on a match,
    /// `None` (fall through to the normal fail-closed path) otherwise — so a real `Option<scalar>`
    /// receiver still declines, never silently opaque.
    fn try_lower_opaque_option_read(
        &mut self,
        fun: ExprId,
        args: &[ExprId],
        callee: FuncId,
    ) -> Option<ValueId> {
        if args.len() != 1 {
            return None;
        }
        // The callee must be `Option::is_some` / `Option::is_none` (by method name; the receiver
        // opacity — checked in `read_opaque_option_lane` — is what makes the read sound).
        let ty::FnDef(def_id, _) = self.thir.exprs[fun].ty.kind() else {
            return None;
        };
        if !matches!(self.tcx.item_name(*def_id).as_str(), "is_some" | "is_none") {
            return None;
        }
        // Peel the receiver borrow to its place, then read the opaque Option lane (fail-closed unless
        // it is a provably-opaque `Ty::Unit` Option field lane).
        let mut a = args[0];
        loop {
            match &self.thir.exprs[a].kind {
                ExprKind::Scope { value, .. } => a = *value,
                ExprKind::Use { source } => a = *source,
                _ => break,
            }
        }
        let place = match &self.thir.exprs[a].kind {
            ExprKind::Borrow { arg, .. } => *arg,
            _ => return None,
        };
        let is_none = self.tcx.item_name(*def_id).as_str() == "is_none";
        let (recv, lane_ty) = self.read_opaque_option_lane(place)?;
        // Trust (wave-RS): a `Ty::Bool` DISCRIMINANT lane (flag-ON only — see
        // `read_opaque_option_lane`) answers is_some/is_none DIRECTLY: the lane value IS the
        // discriminant (`Some` ⇒ true — the write side stores `const bool true/false` for the
        // literal ctors and fails closed on every other RHS), so `is_some` is the read itself and
        // `is_none` its Select-negation (the same `!b` idiom the Unary-Not arm emits). The result
        // is a REAL guard value — the enclosing branch becomes a RESOLVABLE test on the lane, not
        // an opaque nondet. `contains_call` is still FORCED although no call is emitted: the bool
        // lane is an ABSTRACTION of the Option's bytes, so the body must stay structurally NotRun
        // (never interpreted/flipped/spliced — CLEAN-ONLY, the same posture the opaque call had).
        if lane_ty == Ty::Bool {
            self.contains_call = true;
            if !is_none {
                return Some(recv);
            }
            let false_const = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                    .with_result(false_const),
            );
            let true_const = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                    .with_result(true_const),
            );
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::Select {
                    ty: Ty::Bool,
                    cond: recv,
                    then_val: false_const,
                    else_val: true_const,
                })
                .with_result(res),
            );
            return Some(res);
        }
        let res = self.fresh();
        self.contains_call = true;
        self.push_node(InstrNode::new(Inst::Call { callee, args: vec![recv] }).with_result(res));
        Some(res)
    }

    /// Trust (wave-ER): the admissible `let`-condition pattern shapes — a single enum-VARIANT
    /// pattern (`Some(sb)`, `Err(e)`, `None`) whose subpatterns are each `_` or a BY-VALUE,
    /// subpattern-free binding. Returns the binding vars, or `None` (the caller fails closed)
    /// for anything else: by-ref/`@`/nested subpatterns, non-variant patterns, or-patterns.
    /// Trust (wave-SEAM): the VARIANT a `let`-condition pattern tests, as the value-lane's
    /// `Some`-test flag — `Some(true)` for a `Some(..)`-variant pattern (Option variant
    /// index 1, fixed by core's declaration order), `Some(false)` for a `None` pattern,
    /// `None` for any non-variant pattern. MEANINGFUL ONLY when the scrutinee is the Option
    /// lang item (the value-lane admission checks that before consuming this); on any other
    /// enum the index-1 reading is nonsense and the lane never fires.
    fn option_pat_variant_test(pat: &Pat<'tcx>) -> Option<bool> {
        match &pat.kind {
            PatKind::Variant { variant_index, .. } => Some(variant_index.as_u32() == 1),
            _ => None,
        }
    }

    fn let_pat_bindings(&self, pat: &Pat<'tcx>) -> Option<Vec<LocalVarId>> {
        match &pat.kind {
            PatKind::Variant { subpatterns, .. } => {
                let mut out = Vec::new();
                for sp in subpatterns {
                    match &sp.pattern.kind {
                        PatKind::Wild => {}
                        PatKind::Binding {
                            var,
                            mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                            subpattern: None,
                            ..
                        } => out.push(*var),
                        _ => return None,
                    }
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// Trust (wave-ER): lower a `let PAT = scrut` CONDITION (`ExprKind::Let` — let-chains /
    /// `if let`; also the test half of let-`else`, see `lower_stmt`) over an OPAQUE enum value,
    /// producing the test's Bool result. The real erase/drain shapes:
    ///
    ///   `if let Some(sb) = self.storage.scrollback.as_mut() && let Err(e) = sb.clear() { … }`
    ///   `let Some(scrollback) = self.storage.scrollback.as_mut() else { …; return; };`
    ///
    /// ADMISSION (all fail-closed with precise tags):
    ///   * the scrutinee's type is an ADT ENUM whose value shape is NON-pure
    ///     (`!is_pure_value_shape(fat_shape)`) — the opaque-lane family (a data enum, an
    ///     `Option`/`Result` whose payload carries a ptr/Vec/opaque). A PURE enum
    ///     (`Option<u64>`, a scalar-payload `Result`) keeps declining: a projected-able enum
    ///     value must never silently ride the opaque channel (the same discipline as
    ///     `read_opaque_option_lane`).
    ///   * the pattern is a variant test with only `_`/by-value bindings
    ///     (`let_pat_bindings`), none of them promoted (`&mut`-borrowed) locals.
    ///   * the scrutinee itself lowers (typically an opaque `call @Option::as_mut(<lane>)` /
    ///     `call @clear(<carrier>)` via the wave-MC receiver-value machinery) to a
    ///     non-borrow-ptr value.
    ///
    /// EMISSION + SOUNDNESS: the variant TEST on an opaque value is unknowable at this
    /// abstraction, so the result is `Inst::Undef { Bool }` — an ARBITRARY bool. The enclosing
    /// `if`/`&&` CFG then explores BOTH arms; downstream (the temporal extractor) this is the
    /// opaque-branch NONDETERMINISTIC split — a sound over-approximation for safety
    /// obligations: only the test's SELECTION is forgotten, never an effect (both arms'
    /// projected effects are lowered and must prove). The pattern's payload BINDINGS bind to
    /// the scrutinee's own opaque value at `Ty::Unit` (the payload of an opaque enum is itself
    /// opaque) and join `opaque_carrier_locals`: their only pointer-flavored consumer is the
    /// method-receiver value carrier. `contains_call` is FORCED — the body is structurally
    /// NotRun, so the eager-UB `Undef` is never interpreted, and the flip differential fails
    /// closed on it (CLEAN-ONLY, the wave-28 posture).
    fn lower_let_opaque_test(
        &mut self,
        span: rustc_span::Span,
        scrut: ExprId,
        binds: Option<Vec<LocalVarId>>,
        variant_test: Option<bool>,
    ) -> Option<ValueId> {
        let scrut_rty = self.thir.exprs[scrut].ty;
        if !matches!(scrut_rty.kind(), ty::Adt(a, _) if a.is_enum()) {
            self.unsupported.push((format!("{span:?}"), "Let(non-enum scrutinee)"));
            return None;
        }
        // Trust (wave-SEAM): the OPTION-DISCRIMINANT VALUE-LANE test — the real consumer
        // seam `if let Some(ev) = evicted` (aterm-gui temporal.rs:127) where `evicted` is a
        // LOCAL whose bound value is a PROVEN lane discriminant (`option_lane_values`: the
        // `None` ctor const, a local `pop_front() -> Option<Event>` return, or their if/else
        // join). Unlike the opaque channel below, the test result is the REAL `Ty::Bool`
        // value (`Some` pattern: the discriminant itself; `None` pattern: its negation via
        // the read side's const/`select` idiom) — no `Undef`, so a temporal extractor can
        // RESOLVE the branch per-path instead of taking the nondeterministic split. The
        // payload bindings ride the wave-ER carrier discipline unchanged (the payload of a
        // lane Option is abstracted — bound to the scrutinee value at `Ty::Unit`, joined to
        // `opaque_carrier_locals`); `contains_call` is FORCED (the lane is an abstraction —
        // CLEAN-ONLY `NotRun`, the ctor/read-side posture). ADMISSION is deliberately
        // narrower than the opaque channel and entirely NON-EMITTING before it commits:
        //   * the flag is on, the scrutinee's rustc ty is the Option lang item AND
        //     `is_opaque_lane_enum` (exactly the shapes `map_ty` lanes at `Ty::Bool`);
        //   * the pattern is a variant test `let_pat_bindings` admits, with a KNOWN
        //     Option variant (`variant_test`);
        //   * the scrutinee peels to a plain LOCAL (`place_local`) whose CURRENT SSA
        //     binding is LEDGERED — an extern-call result, a param, a field read, a merged
        //     unknown, or any non-local scrutinee falls through to the pre-wave paths
        //     VERBATIM (tags, emission order, flag-off byte-identity all preserved).
        if let Some(pat_is_some) = variant_test {
            if option_flag_lanes_enabled()
                && matches!(scrut_rty.kind(), ty::Adt(a, _)
                    if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
                && self.is_opaque_lane_enum(scrut_rty)
            {
                let lane_val = self
                    .place_local(scrut)
                    .filter(|v| !self.is_promoted(*v))
                    .and_then(|v| last_value(&self.locals, v))
                    .filter(|sv| self.option_lane_values.contains(sv));
                if let Some(sv) = lane_val {
                    let Some(binds) = binds else {
                        self.unsupported.push((format!("{span:?}"), "Let(unsupported pattern)"));
                        return None;
                    };
                    if binds.iter().any(|v| self.is_promoted(*v)) {
                        self.unsupported.push((format!("{span:?}"), "Let(promoted binding)"));
                        return None;
                    }
                    for var in &binds {
                        self.set_local(*var, sv, Ty::Unit);
                        if !self.opaque_carrier_locals.contains(var) {
                            self.opaque_carrier_locals.push(*var);
                        }
                    }
                    self.contains_call = true;
                    if pat_is_some {
                        return Some(sv);
                    }
                    // `let None = …`: the negation, spelled as the read side's
                    // const-false/const-true `select` idiom.
                    let false_const = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                            .with_result(false_const),
                    );
                    let true_const = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                            .with_result(true_const),
                    );
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Select {
                            ty: Ty::Bool,
                            cond: sv,
                            then_val: false_const,
                            else_val: true_const,
                        })
                        .with_result(res),
                    );
                    return Some(res);
                }
            }
        }
        if is_pure_value_shape(&self.fat_shape(scrut_rty, &mut Vec::new())) {
            // The fail-closed tooth: a pure-value (projected-able) enum never opaques.
            self.unsupported.push((format!("{span:?}"), "Let(pure-value scrutinee)"));
            return None;
        }
        let Some(binds) = binds else {
            self.unsupported.push((format!("{span:?}"), "Let(unsupported pattern)"));
            return None;
        };
        if binds.iter().any(|v| self.is_promoted(*v)) {
            // A `&mut`-borrowed binding would need a real slot; the opaque SSA bind has none.
            self.unsupported.push((format!("{span:?}"), "Let(promoted binding)"));
            return None;
        }
        let sv = match self.lower_expr(scrut) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Let(scrutinee unsupported)"));
                return None;
            }
        };
        if self.is_borrow_ptr(sv) {
            self.unsupported.push((format!("{span:?}"), "Let(borrow-ptr scrutinee)"));
            return None;
        }
        for var in &binds {
            self.set_local(*var, sv, Ty::Unit);
            if !self.opaque_carrier_locals.contains(var) {
                self.opaque_carrier_locals.push(*var);
            }
        }
        self.contains_call = true;
        let b = self.fresh();
        self.push_node(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(b));
        Some(b)
    }

    /// Trust (wave-ER): the READ-ONLY-ESCAPE `for`-LOOP SUMMARY — the erase ring-rebuild
    /// shape:
    ///
    /// ```text
    /// for i in 0..self.storage.visible_rows {
    ///     let idx = (live_top + i as usize) % self.storage.rows.len();
    ///     let mut row = unsafe { Row::new(self.storage.cols, &mut new_pages) };
    ///     row.copy_from(&self.storage.rows[idx]);
    ///     new_rows.push(row);
    /// }
    /// ```
    ///
    /// A whole `for` expression whose desugar has always declined (the `mut iter` binding)
    /// is lowered as an OPAQUE SUMMARY — *no* loop CFG, only a HAVOC rebind of every
    /// region-external local the region can mutate — when a structural THIR scan
    /// (`foreach_summary_scan`) PROVES the region's only write channels are plain LOCALS:
    ///
    ///   * every `Assign`/`AssignOp` LHS resolves to a local (`place_local`);
    ///   * every `&mut` borrow targets a plain local (so a callee can mutate ONLY locals
    ///     handed to it; shared borrows are read-only by type); raw borrows refuse;
    ///   * no control-flow escape: no `return`/`become`/`yield`, no `break`-with-value, and
    ///     every `break`/`continue` label targets a scope INSIDE the region;
    ///   * no closures (captures could smuggle a write channel out), no inline asm, no
    ///     static/thread-local refs, no `ref mut` pattern bindings (they alias the scrutinee
    ///     place), no unsafe-binder ops.
    ///
    /// SOUNDNESS of the summary: with the write channels confined to locals, the loop's only
    /// effects visible OUTSIDE the region are the final values of those locals — which the
    /// summary havocs (`Inst::Undef` at the local's declared type: "an unknown value", the
    /// honest post-state; `contains_call` is forced ⇒ NotRun, so the eager-UB `Undef` is
    /// never interpreted and the flip differential fails closed — CLEAN-ONLY). Every READ
    /// the region performs (nested `self.storage.…` places included) is dropped: reads are
    /// effect-free in the value-aggregate model, and callees can reach non-local state only
    /// through the gated borrow channels (no globals alias the protocol state — the model's
    /// standing posture). A region that panics/diverges midway never reaches the fn's `ret`,
    /// which the pipeline already models by excluding non-returning paths (the same posture
    /// as diverging asserts). Writes through an OPAQUE-CARRIER deref (`*scrollback` — the
    /// drain transfer loop) are deliberately REFUSED here: that loop's data flow IS the
    /// conservation evidence (`retained → tiered store`), and summarizing it away would erase
    /// exactly what the temporal extractor must see — drain therefore keeps declining, and
    /// the honest ledger keeps it declared.
    ///
    /// Returns `true` iff the summary was emitted; `false` falls back to the normal
    /// (pre-existing, declining) path with NO state changes and NO tags.
    fn try_lower_foreach_summary(
        &mut self,
        expr_ty: RustcTy<'tcx>,
        _span: rustc_span::Span,
        scrutinee: ExprId,
        arm_ids: &[ArmId],
    ) -> bool {
        // Diagnostics channel (TRUST_ER_DEBUG=1): the refusal reason, for probe-driven
        // iteration. The summary itself never depends on it.
        let debug_refuse = |why: &str| {
            if std::env::var_os("TRUST_ER_DEBUG").is_some_and(|v| v == "1") {
                eprintln!("wave-ER for-summary REFUSED in {:?}: {why}", self.body_def);
            }
            false
        };
        // A `for` expression is unit-typed; anything else is not the shape (defensive).
        if !expr_ty.is_unit() {
            return debug_refuse("non-unit for expr");
        }
        let mut scan = ForSummaryScan::default();
        if let Err(e) = self.foreach_summary_scan(scrutinee, &mut scan) {
            return debug_refuse(&format!("scrutinee: {e}"));
        }
        for aid in arm_ids {
            let (pat_ok, guard, body) = {
                let arm = &self.thir.arms[*aid];
                (Self::scan_pat_bindings(&arm.pattern, &mut scan.declared), arm.guard, arm.body)
            };
            if !pat_ok {
                return debug_refuse("ref-mut arm pattern binding");
            }
            if let Some(g) = guard {
                if let Err(e) = self.foreach_summary_scan(g, &mut scan) {
                    return debug_refuse(&format!("guard: {e}"));
                }
            }
            if let Err(e) = self.foreach_summary_scan(body, &mut scan) {
                return debug_refuse(&format!("body: {e}"));
            }
        }
        // Every break/continue label must target a scope seen INSIDE the region.
        if !scan.jumps.iter().all(|j| scan.scopes.contains(j)) {
            return debug_refuse("break/continue label escapes the region");
        }
        // The HAVOC set: region-external locals the region can mutate. Each must be a
        // currently-BOUND, non-slot SSA local with a known declared type (a slot-promoted
        // scalar or an unbound local refuses the summary — fail-closed, the pre-existing
        // decline stands).
        let mut havoc: Vec<(LocalVarId, Ty)> = Vec::new();
        for var in &scan.mutated {
            if scan.declared.contains(var) {
                continue; // declared inside the region — dead after it.
            }
            if self.promoted_slot(*var).is_some() || self.local_value(*var).is_none() {
                return debug_refuse("mutated external local is slot-promoted or unbound");
            }
            let Some(ty) = self.local_ty(*var) else {
                return debug_refuse("mutated external local has no declared ty");
            };
            if !havoc.iter().any(|(v, _)| v == var) {
                havoc.push((*var, ty));
            }
        }
        // Emit: force NotRun, then one `undef <declared ty>` rebind per mutated external
        // local. Nothing else — the region's reads and its internal control flow are dropped.
        self.contains_call = true;
        for (var, ty) in havoc {
            let h = self.fresh();
            self.push_node(InstrNode::new(Inst::Undef { ty: ty.clone() }).with_result(h));
            self.set_local(var, h, ty);
        }
        true
    }

    /// Trust (wave-ER): collect every by-value/by-ref binding var of `pat` into `out`;
    /// `false` (refuse the summary) on a `ref mut` binding — a mutable alias into the
    /// scrutinee place would be a write channel the local gate cannot see.
    fn scan_pat_bindings(pat: &Pat<'tcx>, out: &mut Vec<LocalVarId>) -> bool {
        let mut ok = true;
        pat.walk_always(|p| {
            if let PatKind::Binding { var, mode, .. } = &p.kind {
                if matches!(
                    mode,
                    rustc_hir::BindingMode(rustc_hir::ByRef::Yes(_, rustc_hir::Mutability::Mut), _)
                ) {
                    ok = false;
                }
                if !out.contains(var) {
                    out.push(*var);
                }
            }
        });
        ok
    }

    /// Trust (wave-DR): peel `Scope`/`Use`/`NeverToAny` wrappers to the underlying expr
    /// (the desugar wraps arm bodies in scopes; the `break` arm's `!` type adds a
    /// never-to-any coercion at unit joins).
    fn peel_wrappers(&self, mut e: ExprId) -> ExprId {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::NeverToAny { source } => e = *source,
                _ => break,
            }
        }
        e
    }

    /// Trust (wave-DR): lower a `for`-loop desugar match VISIBLY — a real back-edge CFG —
    /// after the wave-ER read-only-escape summary REFUSED it (the loop has a write channel
    /// the local gate cannot see, e.g. the real drain transfer loop's
    /// `scrollback.push_line(line)` through the opaque-carrier payload).
    ///
    /// rustc's `lower_expr_for` emits exactly TWO `MatchSource::ForLoopDesugar` shapes:
    ///
    /// ```text
    ///   OUTER: match IntoIterator::into_iter(<head>) { mut iter => loop { <inner> } }
    ///   INNER: match Iterator::next(&mut iter) { None => break, Some(<pat>) => <body> }
    /// ```
    ///
    /// Each dispatches by arm count; any other shape fails closed with a precise tag
    /// (this path is reached only for `ForLoopDesugar`, never a user `match`).
    ///
    /// SOUNDNESS — why the emitted CFG is faithful evidence (the temporal extractor
    /// reads it as such; never summarize-by-erasure):
    ///   * the OUTER match is an irrefutable single-binding destructure — a `let`:
    ///     the iterator init value binds as an opaque SSA carrier (the wave-ER
    ///     non-pure-aggregate local discipline; the desugar `&mut iter`s it at every
    ///     `next`, and an ADT iterator has no faithful scalar-slot model);
    ///   * the INNER match is semantically `if let Some(<pat>) = next(iter) { <body> }
    ///     else { break }`: the variant TEST on the opaque `Option<Item>` value is
    ///     `Undef Bool` (the `lower_let_opaque_test` admission + NotRun posture —
    ///     `contains_call` forced, both arms explored downstream as the opaque-branch
    ///     nondeterministic split), the payload binds as an opaque carrier, and the
    ///     `None` arm lowers its real `break` (a `Br` to the enclosing loop's exit).
    ///     LANE CONTRACT (the extractor's transfer-loop recognizer leans on this): a
    ///     loop-header block of the emitted shape `%opt = call @next(<iter>); %t =
    ///     undef bool; condbr %t → body | exit` comes ONLY from this desugar (or the
    ///     manually-written `if let Some(x) = iter.next()` loop with identical
    ///     exhaustion semantics) — the exit edge IS the `None` (iterator-exhausted)
    ///     arm, and the body arm's payload IS that call's result. A PURE-value
    ///     `Option` item (a range loop's `Option<i32>`) never opaques — the
    ///     `lower_let_opaque_test` gate keeps it declining, exactly as before.
    fn lower_for_desugar(
        &mut self,
        expr_ty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arm_ids: &[ArmId],
    ) -> Option<ValueId> {
        // A `for` expression (and both desugar matches) is unit-typed.
        if !expr_ty.is_unit() {
            self.unsupported.push((format!("{span:?}"), "ForDesugar(non-unit match)"));
            return None;
        }
        match arm_ids {
            [arm] => self.lower_for_desugar_outer(span, scrutinee, *arm),
            [a, b] => self.lower_for_desugar_inner(expr_ty, span, scrutinee, [*a, *b]),
            _ => {
                self.unsupported.push((format!("{span:?}"), "ForDesugar(arm count)"));
                None
            }
        }
    }

    /// Trust (wave-DR): the OUTER `for` desugar match — an irrefutable whole-value
    /// `mut iter` binding over the `into_iter(<head>)` call. Lower the scrutinee, bind
    /// the iterator local as an OPAQUE SSA CARRIER (the wave-ER discipline — see
    /// `lower_for_desugar`), then lower the arm body (the `loop { … }`) on the normal
    /// path. Fail-closed: a non-binding pattern, an unloweable/borrow-ptr scrutinee, or
    /// a NON-opaque iterator type (a pure-value `Range` must never silently opaque —
    /// scalar iterators keep declining).
    fn lower_for_desugar_outer(
        &mut self,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arm: ArmId,
    ) -> Option<ValueId> {
        let (var, body) = {
            let arm = &self.thir.arms[arm];
            let var = match &arm.pattern.kind {
                PatKind::Binding {
                    var,
                    mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                    subpattern: None,
                    ..
                } => *var,
                _ => {
                    self.unsupported.push((format!("{span:?}"), "ForDesugar(iterator pattern)"));
                    return None;
                }
            };
            (var, arm.body)
        };
        let scrut_rty = self.thir.exprs[scrutinee].ty;
        let v = match self.lower_expr(scrutinee) {
            Some(v) => v,
            None => {
                self.unsupported
                    .push((format!("{span:?}"), "ForDesugar(iterator init unsupported)"));
                return None;
            }
        };
        if self.is_borrow_ptr(v) {
            self.unsupported.push((format!("{span:?}"), "ForDesugar(iterator init borrow ptr)"));
            return None;
        }
        // Opaque-carrier admission (mirrors the `lower_stmt` promoted non-scalar `let`
        // arms): a registered opaque-carrying aggregate binds at its opaque struct ty;
        // any other NON-pure ADT binds as a fully-opaque `Ty::Unit`; a pure-value shape
        // (`Range<u16>` — a faithful value model would exist) fails closed.
        let bound_ty = if let Some(oty) = self.opaque_local_aggregate_ty(scrut_rty) {
            oty
        } else if matches!(scrut_rty.kind(), ty::Adt(..))
            && !is_pure_value_shape(&self.fat_shape(scrut_rty, &mut Vec::new()))
        {
            Ty::Unit
        } else {
            self.unsupported.push((format!("{span:?}"), "ForDesugar(non-opaque iterator)"));
            return None;
        };
        self.set_local(var, v, bound_ty);
        if !self.opaque_carrier_locals.contains(&var) {
            self.opaque_carrier_locals.push(var);
        }
        // The arm body is the `loop { … }` — the normal path (lower_loop) emits the
        // real back-edge CFG; the inner desugar match lowers inside it.
        self.lower_expr(body)
    }

    /// Trust (wave-DR): the INNER `for` desugar match —
    /// `match next(&mut iter) { None => break, Some(<pat>) => <body> }` — lowered as
    /// the equivalent `if let Some(<pat>) = next(&mut iter) { <body> } else { break }`:
    /// the scrutinee call + opaque variant test + payload carrier binding ride
    /// `lower_let_opaque_test` (its admission gates verbatim — a pure-value `Option`
    /// item never opaques), and the two arms ride the `lower_if` CFG machinery (the
    /// `break` arm seals with a `Br` to the enclosing loop's exit).
    fn lower_for_desugar_inner(
        &mut self,
        expr_ty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: [ArmId; 2],
    ) -> Option<ValueId> {
        // Classify the two arms: the EXIT arm (a bare-variant pattern whose body peels
        // to a value-less `break`) and the PAYLOAD arm (a variant pattern admitted by
        // `let_pat_bindings`). Exactly one of each, else fail closed.
        let classify = |this: &Self, aid: ArmId| -> (bool, Option<Vec<LocalVarId>>, ExprId) {
            let arm = &this.thir.arms[aid];
            let is_exit = matches!(
                &arm.pattern.kind,
                PatKind::Variant { subpatterns, .. } if subpatterns.is_empty()
            ) && matches!(
                &this.thir.exprs[this.peel_wrappers(arm.body)].kind,
                ExprKind::Break { value: None, .. }
            );
            let binds = this.let_pat_bindings(&arm.pattern);
            (is_exit, binds, arm.body)
        };
        let (a_exit, a_binds, a_body) = classify(self, arms[0]);
        let (b_exit, b_binds, b_body) = classify(self, arms[1]);
        let (binds, payload_body, exit_body) = match (a_exit, b_exit) {
            (true, false) => (b_binds, b_body, a_body),
            (false, true) => (a_binds, a_body, b_body),
            _ => {
                self.unsupported.push((format!("{span:?}"), "ForDesugar(inner arm shape)"));
                return None;
            }
        };
        if binds.is_none() {
            self.unsupported.push((format!("{span:?}"), "ForDesugar(item pattern)"));
            return None;
        }
        // Scrutinee call + opaque variant test + payload carrier binds (admission
        // gates + tags inside; the wrapper tag mirrors the let-`else` convention).
        // Trust (wave-SEAM): `variant_test` is deliberately `None` — the desugar's
        // scrutinee is the iterator's `next()` CALL, never a plain local, so the
        // value-lane arm could not fire anyway (its `place_local` admission refuses);
        // passing `None` keeps this path byte-identical by construction.
        let Some(test) = self.lower_let_opaque_test(span, scrutinee, binds, None) else {
            self.unsupported.push((format!("{span:?}"), "ForDesugar(next test unsupported)"));
            return None;
        };
        // The same CFG as `if <test> { <payload body> } else { break }`.
        self.lower_if_value(expr_ty, span, test, payload_body, Some(exit_body))
    }

    /// Trust (wave-ER): the structural READ-ONLY-ESCAPE scan for `try_lower_foreach_summary`
    /// — an ALLOW-LIST THIR walk (an unlisted `ExprKind` refuses, so a new construct can only
    /// make the gate MORE conservative). Collects: locals the region MUTATES (assign targets +
    /// `&mut`-borrow targets), locals DECLARED in the region (let/match/let-condition pattern
    /// bindings), scopes seen, and `break`/`continue` labels for the containment check.
    fn foreach_summary_scan(&self, e: ExprId, s: &mut ForSummaryScan) -> Result<(), &'static str> {
        match &self.thir.exprs[e].kind {
            ExprKind::Scope { region_scope, value, .. } => {
                s.scopes.push(*region_scope);
                self.foreach_summary_scan(*value, s)
            }
            ExprKind::Use { source: v }
            | ExprKind::NeverToAny { source: v }
            | ExprKind::PointerCoercion { source: v, .. }
            | ExprKind::Cast { source: v }
            | ExprKind::PlaceTypeAscription { source: v, .. }
            | ExprKind::ValueTypeAscription { source: v, .. } => self.foreach_summary_scan(*v, s),
            ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::VarRef { .. } => Ok(()),
            ExprKind::Field { lhs, .. } => self.foreach_summary_scan(*lhs, s),
            ExprKind::Deref { arg } | ExprKind::Unary { arg, .. } => {
                self.foreach_summary_scan(*arg, s)
            }
            ExprKind::Index { lhs, index } => {
                self.foreach_summary_scan(*lhs, s)?;
                self.foreach_summary_scan(*index, s)
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
                self.foreach_summary_scan(*lhs, s)?;
                self.foreach_summary_scan(*rhs, s)
            }
            ExprKind::Borrow { borrow_kind, arg } => {
                if matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }) {
                    // A `&mut` write channel: admissible ONLY to a plain local. THIR
                    // wraps `&mut` call args in a REBORROW (`Borrow{Mut, Deref{Borrow{
                    // Mut, VarRef(x)}}}`), so peel with `reborrow_target` — which
                    // bottoms at the LOCAL for exactly the plain-local shapes and
                    // returns `Ptr`/`NotAPlace` for everything else (`&mut *carrier`,
                    // `&mut a[i]`, `&mut s.f` — all refused: a write channel the local
                    // gate cannot see). The peeled place expr carries no other
                    // subexpressions, so nothing effectful is skipped.
                    match self.reborrow_target(*arg, true) {
                        ReborrowTarget::Local(var) => {
                            if !s.mutated.contains(&var) {
                                s.mutated.push(var);
                            }
                            Ok(())
                        }
                        _ => Err("mut-borrow of a non-local place"),
                    }
                } else {
                    // Shared/Fake — read-only by type; walk for nested effects.
                    self.foreach_summary_scan(*arg, s)
                }
            }
            ExprKind::Assign { lhs, rhs } | ExprKind::AssignOp { lhs, rhs, .. } => {
                let Some(var) = self.place_local(*lhs) else {
                    return Err("write to a non-local place");
                };
                if !s.mutated.contains(&var) {
                    s.mutated.push(var);
                }
                self.foreach_summary_scan(*rhs, s)
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                self.foreach_summary_scan(*cond, s)?;
                self.foreach_summary_scan(*then, s)?;
                match else_opt {
                    Some(el) => self.foreach_summary_scan(*el, s),
                    None => Ok(()),
                }
            }
            ExprKind::Let { expr, pat } => {
                if !Self::scan_pat_bindings(pat, &mut s.declared) {
                    return Err("ref-mut pattern binding");
                }
                self.foreach_summary_scan(*expr, s)
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.foreach_summary_scan(*scrutinee, s)?;
                for aid in arms.iter() {
                    let (pat_ok, guard, body) = {
                        let arm = &self.thir.arms[*aid];
                        (
                            Self::scan_pat_bindings(&arm.pattern, &mut s.declared),
                            arm.guard,
                            arm.body,
                        )
                    };
                    if !pat_ok {
                        return Err("ref-mut pattern binding");
                    }
                    if let Some(g) = guard {
                        self.foreach_summary_scan(g, s)?;
                    }
                    self.foreach_summary_scan(body, s)?;
                }
                Ok(())
            }
            ExprKind::Block { block } => {
                let (stmts, tail) = {
                    let blk = &self.thir.blocks[*block];
                    (blk.stmts.iter().copied().collect::<Vec<StmtId>>(), blk.expr)
                };
                for sid in stmts {
                    let (pat_ok, init, else_blk) = {
                        match &self.thir.stmts[sid].kind {
                            StmtKind::Expr { expr, .. } => {
                                self.foreach_summary_scan(*expr, s)?;
                                continue;
                            }
                            StmtKind::Let { pattern, initializer, else_block, .. } => (
                                Self::scan_pat_bindings(pattern, &mut s.declared),
                                *initializer,
                                *else_block,
                            ),
                        }
                    };
                    if !pat_ok {
                        return Err("ref-mut pattern binding");
                    }
                    if let Some(init) = init {
                        self.foreach_summary_scan(init, s)?;
                    }
                    if let Some(eb) = else_blk {
                        let (estmts, etail) = {
                            let blk = &self.thir.blocks[eb];
                            (blk.stmts.iter().copied().collect::<Vec<StmtId>>(), blk.expr)
                        };
                        for es in estmts {
                            match &self.thir.stmts[es].kind {
                                StmtKind::Expr { expr, .. } => {
                                    let expr = *expr;
                                    self.foreach_summary_scan(expr, s)?;
                                }
                                StmtKind::Let { .. } => return Err("nested let-else"),
                            }
                        }
                        if let Some(t) = etail {
                            self.foreach_summary_scan(t, s)?;
                        }
                    }
                }
                match tail {
                    Some(t) => self.foreach_summary_scan(t, s),
                    None => Ok(()),
                }
            }
            ExprKind::Loop { body } => self.foreach_summary_scan(*body, s),
            ExprKind::Break { label, value } => {
                if value.is_some() {
                    return Err("break with value");
                }
                s.jumps.push(*label);
                Ok(())
            }
            ExprKind::Continue { label } => {
                s.jumps.push(*label);
                Ok(())
            }
            ExprKind::Call { fun, args, .. } => {
                self.foreach_summary_scan(*fun, s)?;
                for a in args.iter() {
                    self.foreach_summary_scan(*a, s)?;
                }
                Ok(())
            }
            ExprKind::Tuple { fields } | ExprKind::Array { fields } => {
                for f in fields.iter() {
                    self.foreach_summary_scan(*f, s)?;
                }
                Ok(())
            }
            ExprKind::Repeat { value, .. } => self.foreach_summary_scan(*value, s),
            ExprKind::Adt(adt_expr) => {
                for f in adt_expr.fields.iter() {
                    self.foreach_summary_scan(f.expr, s)?;
                }
                match &adt_expr.base {
                    rustc_middle::thir::AdtExprBase::None => Ok(()),
                    rustc_middle::thir::AdtExprBase::Base(b) => {
                        self.foreach_summary_scan(b.base, s)
                    }
                    rustc_middle::thir::AdtExprBase::DefaultFields(_) => Err("default-fields ctor"),
                }
            }
            // Everything else — RawBorrow, Return/Become/Yield, Closure/UpvarRef, InlineAsm,
            // StaticRef/ThreadLocalRef, ByUse, LoopMatch/ConstContinue, unsafe-binder ops —
            // REFUSES the summary (the pre-existing decline stands).
            _ => Err("out-of-gate construct"),
        }
    }

    /// Trust (realbody store move-out): the SSA-bind type for a `&mut`-borrowed NON-scalar LOCAL
    /// struct that is NOT a pure value (it carries a `Vec`/`Option`/ptr/opaque lane — the real
    /// `let mut store = reflowed.store;` shape, `Store { lines: Vec, .. }`). Such a local is bound as
    /// an SSA value instead of promoted to a scalar slot: its ONLY sound consumer is a method-receiver
    /// `&mut store` — an opaque wave-MC `call @callee` that sets `contains_call` → the body is NotRun
    /// (never interpreted/flipped); a real `&mut store` ARG still declines at its own `Borrow` site.
    ///
    /// SOUNDNESS: `None` (keep declining) for a PURE-VALUE struct — the scalar-slot faithfulness
    /// concern the original decline guards applies only there; a non-pure struct has no faithful
    /// scalar-slot model to be unfaithful to, and its opaque-receiver use is the same NotRun basis as
    /// the field-receiver wave-MC path. We reuse the ALREADY-REGISTERED `Ty::Struct` id (registered at
    /// param binding / the value's read) rather than re-entering `struct_ty_rmw_opaque` — which would
    /// hit its `adt_visit_stack` cycle guard mid-walk (the local's own read already has it in flight).
    /// Trust (wave-EL): `true` iff `rty` is a DATA ENUM the type model declines END-TO-END —
    /// not a registrable general
    /// `Ty::Enum` (`register_enum`) — i.e. EXACTLY the enums `map_ty` collapses to the opaque
    /// `Ty::Unit` lane. This is the single admission predicate every wave-EL operation lane
    /// gates on (Field read, local bind, seed), so a `Ty::Unit` produced by any OTHER decline
    /// (an unmappable non-enum type, a real `()`) never silently rides an enum-only channel.
    ///
    /// A QUERY, not a lowering: any `unsupported` entries the probing map records (nested
    /// field-type walks) are rolled back. A register_enum SUCCESS during the probe commits the
    /// def — the same commit the mapped site performs (dedup'd by `(DefId, args)`), harmless.
    fn is_opaque_lane_enum(&mut self, rty: RustcTy<'tcx>) -> bool {
        let ty::Adt(adt, args) = rty.kind() else {
            return false;
        };
        if !adt.is_enum() {
            return false;
        }
        // Trust (B3-2c T2): register_enum is the SOLE model — an enum it
        // declines IS the opaque lane (the legacy enum_repr_ty middle layer is
        // deleted).
        let mark = self.unsupported.len();
        let opaque = self.register_enum(*adt, *args).is_none();
        self.unsupported.truncate(mark);
        opaque
    }

    fn opaque_local_aggregate_ty(&mut self, rty: RustcTy<'tcx>) -> Option<Ty> {
        // Trust (wave-EL): a `&mut`-borrowed DATA-ENUM local — the REAL
        // `let mut store = reflowed.store; let _ = store.clear();` shape, where `store` is the
        // `ScrollbackStorage` DATA ENUM (the transcription's `Store` struct generalized). The
        // local binds the OPAQUE LANE VALUE (`Ty::Unit` — matching the wave-EL Field-arm read
        // that produced `v`): no scalar slot exists to promote to, and its only sound consumer
        // is the wave-MC opaque method-receiver carrier (`store.clear()` → opaque
        // `call @callee(store)`, `contains_call` ⇒ NotRun). Payload extraction from the local
        // still declines at its own arms (`EnumMatch(non-enum mapped ty)`), never through here.
        if self.is_opaque_lane_enum(rty) {
            return Some(Ty::Unit);
        }
        let ty::Adt(adt, _gargs) = rty.kind() else {
            return None;
        };
        if !(adt.is_struct() && adt.did().is_local()) {
            return None;
        }
        // Pure-value struct → keep declining (the original scalar-slot faithfulness gate).
        if is_pure_value_shape(&self.fat_shape(rty, &mut Vec::new())) {
            return None;
        }
        // Reuse the registered id (dedup by (DefId, GenericArgs), B3-4 — a DefId-only
        // probe would alias a different instantiation's shape); fall back to a fresh
        // map only if this exact instantiation is unregistered.
        let did = adt.did();
        let ty::Adt(_, rargs) = rty.kind() else { return None };
        let registered = self
            .struct_ids
            .iter()
            .find(|(d, a, _)| *d == did && *a == *rargs)
            .map(|(_, _, id)| Ty::Struct(*id));
        Some(registered.unwrap_or_else(|| self.map_ty(rty)))
    }

    fn lower_call_args(
        &mut self,
        expr_span: rustc_span::Span,
        args: &[ExprId],
        diverges: bool,
        recv_fallback: bool,
        unit_sink: bool,
    ) -> Option<Vec<ValueId>> {
        let mut arg_vals: Vec<ValueId> = Vec::with_capacity(args.len());
        let mut collect_failed = false;
        for &a in args {
            // Trust (wave-RS, ON BY DEFAULT `TRUST_SHARED_RECV_PLACE`; `=0` disables): a SHARED borrow of a
            // NON-scalar field-chain lane in explicit-call position PREEMPTS the general
            // Borrow lowering (which would otherwise succeed UNATTRIBUTABLY — the raw base
            // ptr at offset 0 / a byte-offset gep) and carries the receiver PLACE instead
            // (the wave-MC `&mut` treatment extended to `&`). Flag off: dead code,
            // byte-identical dumps. Gated to explicit method/fn calls (`recv_fallback`).
            if recv_fallback {
                if let Some(v) = self.try_lower_shared_recv_place(a) {
                    arg_vals.push(v);
                    continue;
                }
            }
            let mark = self.unsupported.len();
            match self.lower_expr(a) {
                Some(v) => arg_vals.push(v),
                None => {
                    // Trust (wave-MC): a method-receiver borrow of a nested field
                    // place — `&mut self.lazy_buffer` — has no address, so the
                    // general Borrow arm declined above. Lower it as the receiver
                    // field VALUE instead (carrying the place-path for the temporal
                    // method-effect KB; CLEAN-ONLY, contains_call → NotRun). Undo the
                    // borrow's decline tags on success. Gated to explicit method/fn
                    // calls (`recv_fallback`), never operator desugars.
                    if recv_fallback {
                        if let Some(v) = self.try_lower_receiver_place_value(a) {
                            // Trust (B3-2c seam guard): value-for-pointer carrier
                            // (either internal path) — CLEAN-ONLY, seam-ineligible.
                            self.place_path_carrier = true;
                            self.unsupported.truncate(mark);
                            arg_vals.push(v);
                            continue;
                        }
                    }
                    // Trust (wave-28): an effect-free CONSTANT arg to a DIVERGING (`-> !`) callee
                    // that cannot lower is DROPPED rather than failing the whole call closed. The
                    // canonical case is `core::panicking::assert_failed(kind, &l, &r,
                    // Option::<Arguments>::None)` — the `Option<Arguments>` arg is unmappable
                    // (`Ty(enum-def)`), which is what blocks `assert_eq!`/`assert_ne!`. Soundness:
                    // the call never returns, so the arg's value is unobserved on every path that
                    // continues; and a niladic const (`is_effect_free_const_arg`) has NO side effect
                    // to preserve (Rust evaluates it before the call, but it computes nothing). The
                    // emitted `Inst::Call` still carries the SURVIVING args and keeps
                    // `contains_call = true`, so (a) the interp differential short-circuits the body
                    // to `NotRun` and (b) the flip gate rejects the diverging call as
                    // `DerivedUnsupported` — the short-arity call is thus NEVER interpreted, flipped,
                    // or certified (CLEAN-ONLY). The FuncId is a bodyless-declaration structural
                    // reference with no producer-side arity check (see `admit_callee`), so a
                    // short-arity call is well-formed. The failed arg's OWN tags (pushed deep inside
                    // its `lower_expr`, which emits no IR before failing) are undone so the body can
                    // lower clean. An EFFECTFUL arg (fielded ctor / call / non-const) is never
                    // skipped — dropping it would silently drop an observable side effect.
                    if diverges && self.is_effect_free_const_arg(a) {
                        self.unsupported.truncate(mark);
                        continue;
                    }
                    // Trust (wave-ER, logging/panic-sink format plumbing): an unloweable arg to a
                    // UNIT-returning or DIVERGING callee whose whole subtree is READ-ONLY FORMAT
                    // PLUMBING (`is_read_only_plumbing` — literals/consts, SHARED borrows, pure
                    // ops, ctors, and calls ONLY to `core::fmt` constructors; NO writes, NO `&mut`
                    // / raw borrows, NO other calls, NO control-flow escape) is DROPPED rather
                    // than failing the whole call closed. The canonical case is
                    // `aterm_log::warn!("… {e}")` → `__log(Level, path, format_args!(…),
                    // Some(file), Some(line))` — the `fmt::Arguments` construction is unmappable.
                    //
                    // SOUNDNESS: the dropped subtree computes only shared-read VIEWS (structurally
                    // proven: no write, no `&mut`, and the fmt ctors are pure view-builders — a
                    // documented KB-grade axiom about `core::fmt`); its evaluation has no effect
                    // to preserve, and reads are effect-free in the model. The callee returns
                    // UNIT (no value flows out) or never returns; a projected place can therefore
                    // feed INTO the sink only as a READ (harmless) and never OUT. A subtree
                    // containing any write to any place — projected or not — refuses the walk and
                    // the call keeps failing closed. The emitted short-arity `Inst::Call` keeps
                    // `contains_call = true` (NotRun / never flipped / never certified; the
                    // FuncId is a bodyless declaration with no arity check — wave-28's posture).
                    if (diverges || unit_sink) && self.is_read_only_plumbing(a) {
                        self.unsupported.truncate(mark);
                        continue;
                    }
                    self.unsupported.push((format!("{expr_span:?}"), "Call(unsupported arg)"));
                    // Trust (v2 Phase 0b): in collect-all mode keep walking the REMAINING args so
                    // their subtrees' leaf tags are recorded too ('Call(unsupported arg)' is the
                    // #1 aggregator: 3793 events, 98.6% masked) — then still fail the call closed.
                    if self.collect_all {
                        collect_failed = true;
                        continue;
                    }
                    return None;
                }
            }
        }
        if collect_failed {
            return None;
        }
        Some(arg_vals)
    }

    /// Emit a call using the producer's canonical result convention. Rust `()` has no runtime
    /// value in this IR: a unit-returning function is signed `returns: []`, its `Return` carries no
    /// values, and every call to it must therefore declare zero results as well. Non-unit calls
    /// declare exactly one result. Keeping this decision at the THIR call site prevents linked
    /// interpretation from seeing a malformed one-result-call/zero-result-callee pair.
    fn emit_call(&mut self, inst: Inst, result_rty: RustcTy<'tcx>) -> Option<ValueId> {
        self.contains_call = true;
        let node = InstrNode::new(inst);
        if result_rty.is_unit() {
            self.cur.push(node);
            None
        } else {
            let result = self.fresh();
            self.cur.push(node.with_result(result));
            Some(result)
        }
    }

    /// Trust (wave-28): true iff arg expr `a` (peeling `Scope`/`Use`) is a compile-time,
    /// SIDE-EFFECT-FREE value — a NILADIC (zero-field, no `..base`) enum/struct constructor
    /// (`None`, `AssertKind::Eq`), a literal, or a named const. Only such an arg may be DROPPED when
    /// it fails to lower for a DIVERGING callee: Rust evaluates it before the call, but it computes
    /// nothing, so dropping it drops no observable effect. An arg with FIELD exprs (which may
    /// compute) or a `..base` is NOT effect-free and must never be skipped.
    fn is_effect_free_const_arg(&self, mut a: ExprId) -> bool {
        loop {
            match &self.thir.exprs[a].kind {
                ExprKind::Scope { value, .. } => a = *value,
                ExprKind::Use { source } => a = *source,
                _ => break,
            }
        }
        match &self.thir.exprs[a].kind {
            ExprKind::Adt(e) => {
                e.fields.is_empty() && matches!(e.base, rustc_middle::thir::AdtExprBase::None)
            }
            ExprKind::Literal { .. } | ExprKind::NamedConst { .. } => true,
            _ => false,
        }
    }

    /// Trust (wave-ER): true iff the THIR subtree at `a` is READ-ONLY FORMAT PLUMBING — the
    /// `format_args!` expansion family (`Arguments::new_v1(&[pieces], &[Argument::new_display
    /// (&e)])`, the capture `match (&e,) { args => … }` wrap, `Some(file!())`/`Some(line!())`
    /// ctors). ALLOW-LIST walk (anything unlisted refuses — a new THIR variant can only make
    /// this MORE conservative):
    ///   * values/consts/reads: literals, named/inline consts, locals, field/index/deref
    ///     reads, casts/coercions, type ascriptions;
    ///   * PURE ops: unary/binary/logical (no assignment forms — those are separate kinds);
    ///   * construction: tuples, arrays, ADT ctors (fields + base walked);
    ///   * SHARED/`Fake` borrows only — a `&mut`/raw borrow REFUSES (the whole point: no
    ///     callee can write through what this subtree hands out);
    ///   * control INSIDE the value (the `format_args!` capture match, `if`/`&&` in an
    ///     argument): scrutinee/arms/guards/branches all walked; `break`/`continue`/`return`/
    ///     `yield`/`become` REFUSE (control must not escape the dropped subtree);
    ///   * calls ONLY to `core::fmt` constructors (`Arguments::new_*`, `rt::Argument::new_*`,
    ///     `rt::Count`, …) — pure view-builders (a documented KB-grade axiom about `core::fmt`;
    ///     they allocate nothing and write nothing). ANY other callee refuses.
    /// A refused subtree keeps the call's fail-closed tag — a write to ANY place (projected or
    /// not), a mutable borrow, or an unknown callee inside a format argument is never dropped.
    fn is_read_only_plumbing(&self, e: ExprId) -> bool {
        match &self.thir.exprs[e].kind {
            ExprKind::Scope { value, .. }
            | ExprKind::Use { source: value }
            | ExprKind::NeverToAny { source: value }
            | ExprKind::PointerCoercion { source: value, .. }
            | ExprKind::Cast { source: value }
            | ExprKind::PlaceTypeAscription { source: value, .. }
            | ExprKind::ValueTypeAscription { source: value, .. } => {
                self.is_read_only_plumbing(*value)
            }
            ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::VarRef { .. } => true,
            ExprKind::Field { lhs, .. } => self.is_read_only_plumbing(*lhs),
            ExprKind::Deref { arg } | ExprKind::Unary { arg, .. } => {
                self.is_read_only_plumbing(*arg)
            }
            ExprKind::Index { lhs, index } => {
                self.is_read_only_plumbing(*lhs) && self.is_read_only_plumbing(*index)
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
                self.is_read_only_plumbing(*lhs) && self.is_read_only_plumbing(*rhs)
            }
            ExprKind::Borrow { borrow_kind, arg } => {
                matches!(
                    borrow_kind,
                    rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_)
                ) && self.is_read_only_plumbing(*arg)
            }
            ExprKind::Tuple { fields } | ExprKind::Array { fields } => {
                fields.iter().all(|f| self.is_read_only_plumbing(*f))
            }
            ExprKind::Repeat { value, .. } => self.is_read_only_plumbing(*value),
            ExprKind::Adt(adt_expr) => {
                adt_expr.fields.iter().all(|f| self.is_read_only_plumbing(f.expr))
                    && match &adt_expr.base {
                        rustc_middle::thir::AdtExprBase::None => true,
                        rustc_middle::thir::AdtExprBase::Base(b) => {
                            self.is_read_only_plumbing(b.base)
                        }
                        rustc_middle::thir::AdtExprBase::DefaultFields(_) => false,
                    }
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                self.is_read_only_plumbing(*cond)
                    && self.is_read_only_plumbing(*then)
                    && else_opt.map_or(true, |el| self.is_read_only_plumbing(el))
            }
            ExprKind::Let { expr, .. } => self.is_read_only_plumbing(*expr),
            ExprKind::Match { scrutinee, arms, .. } => {
                self.is_read_only_plumbing(*scrutinee)
                    && arms.iter().all(|aid| {
                        let arm = &self.thir.arms[*aid];
                        arm.guard.map_or(true, |g| self.is_read_only_plumbing(g))
                            && self.is_read_only_plumbing(arm.body)
                    })
            }
            ExprKind::Block { block } => {
                let blk = &self.thir.blocks[*block];
                blk.stmts.iter().all(|sid| match &self.thir.stmts[*sid].kind {
                    StmtKind::Expr { expr, .. } => self.is_read_only_plumbing(*expr),
                    StmtKind::Let { initializer, else_block, .. } => {
                        initializer.map_or(true, |i| self.is_read_only_plumbing(i))
                            && else_block.is_none()
                    }
                }) && blk.expr.map_or(true, |t| self.is_read_only_plumbing(t))
            }
            ExprKind::Call { fun, args, .. } => {
                self.is_fmt_plumbing_callee(*fun)
                    && args.iter().all(|a| self.is_read_only_plumbing(*a))
            }
            // Everything else — Assign/AssignOp, `&mut`/RawBorrow, Loop, Break/Continue/
            // Return/Become/Yield, Closure, UpvarRef, InlineAsm, StaticRef, ThreadLocalRef,
            // unsafe-binder ops, ByUse, LoopMatch/ConstContinue — REFUSES.
            _ => false,
        }
    }

    /// Trust (wave-ER): the `core::fmt` constructor whitelist for `is_read_only_plumbing` —
    /// a `FnDef` callee whose def-path lives under `core::fmt` (`Arguments::new_v1`/
    /// `new_const`, `rt::Argument::new_display`/`new_debug`/…, `rt::Count::*`). These are pure
    /// view-builders (no writes, no allocation) — the ONE KB-grade axiom this walk leans on.
    fn is_fmt_plumbing_callee(&self, fun: ExprId) -> bool {
        let mut f = fun;
        loop {
            match &self.thir.exprs[f].kind {
                ExprKind::Scope { value, .. } => f = *value,
                ExprKind::Use { source } => f = *source,
                _ => break,
            }
        }
        let ty::FnDef(def_id, _) = self.thir.exprs[f].ty.kind() else {
            return false;
        };
        let path = rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(*def_id));
        path.starts_with("core::fmt::") || path.starts_with("std::fmt::")
    }

    /// Trust: resolve a `ReifyFnPointer` coercion source (`fn` item → `fn(…) -> …` value) to the
    /// concrete `DefId` the pointer will call, or a precise fail-closed tag. Mirrors
    /// `resolve_callee`'s gates, but uses `Instance::resolve_for_fn_ptr` — the query codegen
    /// itself uses for this exact coercion — so a `#[track_caller]` target surfaces as
    /// `InstanceKind::ReifyShim` (the reified pointer must call a location-supplying shim;
    /// pointing our `Constant::FnDef` at the plain body would drop that argument): fail closed.
    fn resolve_reify_target(
        &mut self,
        def_id: DefId,
        gen_args: ty::GenericArgsRef<'tcx>,
    ) -> Result<DefId, &'static str> {
        match self.tcx.def_kind(def_id) {
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
            _ => return Err("Reify(unsupported def-kind)"),
        }
        // `resolve_for_fn_ptr` asserts `!is_closure_like(def_id)`; a reify coercion's source is
        // a plain fn item (`ClosureFnPointer` is a different coercion) — checked, not assumed.
        if self.tcx.is_closure_like(def_id) {
            return Err("Reify(closure)");
        }
        if gen_args.has_non_region_param() || gen_args.has_non_region_infer() {
            return Err("Reify(generic fn item)");
        }
        // Same E0391 query-cycle guard as the call paths: normalizing args that
        // mention an unrevealed opaque can demand borrowck of the defining body.
        if gen_args.has_opaque_types() {
            return Err("Reify(opaque type in fn item args)");
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        // Trust: rust 1.99 — `try_normalize_erasing_regions` takes `Unnormalized<T>` (`new_wip`).
        let Ok(gen_args) =
            self.tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(gen_args))
        else {
            return Err("Reify(generic fn item)");
        };
        match ty::Instance::resolve_for_fn_ptr(self.tcx, typing_env, def_id, gen_args) {
            Some(inst) => match inst.def {
                ty::InstanceKind::Item(resolved) => {
                    if self.tcx.is_closure_like(resolved) {
                        Err("Reify(closure)")
                    } else if !self.sig_shapes_coherent(resolved, inst.args) {
                        // Trust (wave-19): same DST-coherence gate as the `resolve_callee` path —
                        // refuse a fn-ptr to an instance whose concrete signature is ABI-incoherent
                        // with the identity-lowered record (a fat `&str`/`&[T]` where the record is
                        // thin, at any nesting depth). Coherent trait-default reifications still admit.
                        Err("Reify(DST-incoherent instantiation)")
                    } else {
                        // Reify the resolved instance — including a trait DEFAULT body — as
                        // `Constant::FnDef(admit_callee(resolved))`; the fn-ptr names the
                        // site-spelled DefId and a non-clean default splices as havoc.
                        Ok(resolved)
                    }
                }
                // ReifyShim (#[track_caller] / KCFI), Virtual, Intrinsic, other shims.
                _ => Err("Reify(instance shim)"),
            },
            None => Err("Reify(generic fn item)"),
        }
    }

    /// Trust: intern a fn-pointer signature `FuncTy` into the per-body pending table, returning
    /// the `FuncTyId` it WILL occupy once `lower_fn` flushes: slot 0 is always the function's
    /// own signature, so position `i` → `FuncTyId(1 + i)`. Dedup by structural equality keeps
    /// the table minimal and the ids deterministic (first-encounter order within the body).
    fn pend_func_ty(&mut self, ft: FuncTy) -> FuncTyId {
        if let Some(i) = self.pending_func_tys.iter().position(|existing| *existing == ft) {
            return FuncTyId::new(1 + i as u32);
        }
        self.pending_func_tys.push(ft);
        FuncTyId::new(self.pending_func_tys.len() as u32)
    }

    /// Trust: intern a `Ty` into the per-body pending module-`types` table (today: only the
    /// element type of a zero-length `[T; 0]` array), returning the `TyId` it WILL occupy once
    /// `lower_fn` flushes. The per-body module's `types` table starts EMPTY (nothing else adds
    /// to it — tripwired at the flush), so position `i` → `TyId(i)`. Dedup by structural
    /// equality, mirroring `pend_func_ty`.
    fn pend_ty(&mut self, ty: Ty) -> trust_ir::TyId {
        if let Some(i) = self.pending_tys.iter().position(|existing| *existing == ty) {
            return trust_ir::TyId::new(i as u32);
        }
        self.pending_tys.push(ty);
        trust_ir::TyId::new((self.pending_tys.len() - 1) as u32)
    }

    /// Trust (B6): intern a first-class `ClosureTy` into the per-body pending table,
    /// returning the `ClosureTyId` it WILL occupy once `lower_fn` flushes (the per-body
    /// `closure_types` table starts EMPTY, so position `i` → `ClosureTyId(i)`). Structural
    /// dedup — `ClosureTy` identity IS `(func, captures)` (the ty#4145 rule), so two source
    /// closures with the same call signature and capture types share one format type.
    fn pend_closure_ty(&mut self, ct: trust_ir::ClosureTy) -> trust_ir::ClosureTyId {
        if let Some(i) = self.pending_closure_tys.iter().position(|existing| *existing == ct) {
            return trust_ir::ClosureTyId::new(i as u32);
        }
        self.pending_closure_tys.push(ct);
        trust_ir::ClosureTyId::new((self.pending_closure_tys.len() - 1) as u32)
    }

    /// Trust: `map_ty` with an explicit failure channel — `None` iff the mapping recorded any
    /// new `unsupported` entry (the inner entry stays, keeping the precise reason), so callers
    /// that must NOT accept a placeholder `Ty::Unit` (e.g. a fn-ptr signature component, where
    /// a placeholder would silently change the sig) can fail closed instead.
    fn map_ty_checked(&mut self, ty: RustcTy<'tcx>) -> Option<Ty> {
        let before = self.unsupported.len();
        let mapped = self.map_ty(ty);
        (self.unsupported.len() == before).then_some(mapped)
    }

    /// Trust: map a `ty::FnPtr` to `Ty::Func(sig)` over a pended per-body `FuncTy`, or `None`
    /// (fail-closed; the caller records "Ty(fn-ptr)"). The admitted fragment:
    ///   * `extern "Rust"`, non-variadic (the emitted `CallIndirect` declares
    ///     `CallingConv::Rust`); `unsafe` fn-ptrs are fine — safety is a check-time property,
    ///     call semantics are identical and unsafeck already ran;
    ///   * every param/return maps cleanly (`map_ty_checked` — no placeholder `Ty::Unit` sig
    ///     holes), with the producer's unit-return convention (`returns: []`);
    ///   * NO higher-order signatures (a param/return containing another `Ty::Func`): splice
    ///     remapping in `crate_module` is deliberately non-recursive, so nesting fails closed
    ///     here (the containment invariant that keeps `Ty::Func` confined to positions the
    ///     splice checks and rewrites).
    /// Late-bound regions under the binder (`for<'a> fn(&'a i32)`) are irrelevant: `map_ty`
    /// erases regions in every arm, so `skip_binder` is sound.
    fn map_fn_ptr_ty(
        &mut self,
        sig_tys: ty::Binder<'tcx, ty::FnSigTys<TyCtxt<'tcx>>>,
        header: ty::FnHeader<TyCtxt<'tcx>>,
    ) -> Option<Ty> {
        // Trust: rust 1.99 — `FnHeader.c_variadic`/`.abi` are now accessor methods, not fields.
        if header.c_variadic() || header.abi() != rustc_abi::ExternAbi::Rust {
            return None;
        }
        let sig = sig_tys.skip_binder();
        let mut params: Vec<Ty> = Vec::new();
        // `FnSigTys::inputs()` is `&'tcx [Ty<'tcx>]` (the `Tys::inputs` impl in
        // rustc_middle/src/ty/sty.rs), so iteration yields `&Ty` — destructure-copy.
        // Trust (wave-EL): a DATA-ENUM param/return would now map "cleanly" to the opaque
        // `Ty::Unit` lane, making it indistinguishable from a real unit in a SPLICED,
        // oracle-compared fn-POINTER signature (an ABI lie at an indirect-call boundary,
        // unlike a direct callee's opaque flow). Fn-ptr sigs keep the PRE-wave posture:
        // an opaque-lane enum anywhere in the signature declines (`Ty(fn-ptr)` at the
        // caller), exactly the "no placeholder `Ty::Unit` sig holes" contract above.
        for &input in sig.inputs().iter() {
            if self.is_opaque_lane_enum(input) {
                return None;
            }
            params.push(self.map_ty_checked(input)?);
        }
        let output = sig.output();
        // Trust (wave-EL): an opaque-lane enum in RETURN position declines, symmetric with the
        // input-parameter guard above (no placeholder `Ty::Unit` holes in a spliced fn-ptr sig).
        let returns = if output.is_unit() {
            Vec::new()
        } else if self.is_opaque_lane_enum(output) {
            return None;
        } else {
            vec![self.map_ty_checked(output)?]
        };
        if params.iter().chain(returns.iter()).any(ty_contains_func) {
            return None;
        }
        Some(Ty::Func(self.pend_func_ty(FuncTy { params, returns, is_vararg: false })))
    }

    /// Trust: resolve an assignment/place LHS to the bare `LocalVarId` it names, peeling the
    /// `Scope`/`Use` wrappers THIR inserts around place expressions. Returns `Some(var)` ONLY for a
    /// direct local variable (`ExprKind::VarRef`); any other place (field/index/deref projection,
    /// `*p`, `a.b`, `a[i]`) returns `None` so the `Assign` arm fails closed — SSA value-versioning a
    /// non-local place would need a memory model we do not have yet.
    fn place_local(&self, mut place: ExprId) -> Option<LocalVarId> {
        loop {
            match &self.thir.exprs[place].kind {
                ExprKind::Scope { value, .. } => place = *value,
                ExprKind::Use { source } => place = *source,
                ExprKind::VarRef { id } => return Some(*id),
                _ => return None,
            }
        }
    }

    /// Trust: peel the THIR REBORROW shape down to the underlying place. THIR wraps every
    /// reference-typed CALL ARGUMENT (and every explicit `&*…` reborrow) as
    /// `Borrow{kind, Deref{ inner }}` — verified shapes (thir-tree, 2026-07-02):
    ///
    ///   * `f(&x)`      → `Borrow{Shared, Deref{Borrow{Shared, VarRef(x)}}}`
    ///   * `f(r)`       → `Borrow{Shared, Deref{VarRef(r)}}`         (r: `&T` binding)
    ///   * `f(&mut x)`  → `Borrow{Mut{TwoPhase}, Deref{Borrow{Mut{Default}, VarRef(x)}}}`
    ///   * `f(&p.a)`    → `Borrow{Shared, Deref{Borrow{Shared, Field{..}}}}`  (NOT a local)
    ///
    /// Starting from the borrow's `arg`, we peel `Scope`/`Use` wrappers and collapse
    /// `Deref{Borrow{…, P}}` layers (`*&place == place`, `*&mut place == place`) — the same
    /// borrow-then-deref-is-the-place identity `array_place_expr` uses — until the chain bottoms
    /// out at:
    ///
    ///   * a bare `VarRef` → `Local(var)` (route to the existing snapshot / promoted-slot
    ///     admissions in the `Borrow` arm);
    ///   * `Deref{ e }` where `e` is a NON-borrow expr of `ty::Ref` type (a ref binding like
    ///     `VarRef(r)`) → `Ptr(e)`: the place is `*r`, whose ADDRESS is `r`'s own value — the
    ///     caller lowers `e` and requires the result to be a KNOWN borrow pointer;
    ///   * anything else (`Field`, `Index`, a raw-pointer deref — the ty gate excludes non-`Ref`
    ///     pointees) → `NotAPlace`: the caller keeps its precise fail-closed tag.
    ///
    /// MUTABILITY gate (`want_mut`): a `&mut` reborrow only peels `Mut{..}` inner borrows and only
    /// accepts `&mut`-typed `Ptr` exprs — `&mut *(&x)` is ill-typed Rust, but this lowering runs at
    /// `mir_built` (before borrowck) so the shape is CHECKED, not assumed. A SHARED reborrow peels
    /// `Shared`/`Fake`/`Mut` alike (`&*r` on `r: &mut T` is the legal shared reborrow).
    fn reborrow_target(&self, mut e: ExprId, want_mut: bool) -> ReborrowTarget {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::VarRef { id } => return ReborrowTarget::Local(*id),
                ExprKind::Deref { arg } => {
                    // Peel Scope/Use around the deref operand before classifying it.
                    let mut inner = *arg;
                    loop {
                        match &self.thir.exprs[inner].kind {
                            ExprKind::Scope { value, .. } => inner = *value,
                            ExprKind::Use { source } => inner = *source,
                            _ => break,
                        }
                    }
                    match &self.thir.exprs[inner].kind {
                        ExprKind::Borrow { borrow_kind, arg: place } => {
                            if want_mut
                                && !matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. })
                            {
                                return ReborrowTarget::NotAPlace;
                            }
                            // `*&place` / `*&mut place` IS `place` — keep peeling.
                            e = *place;
                        }
                        _ if matches!(
                            self.thir.exprs[inner].ty.kind(),
                            ty::Ref(_, _, m)
                                if !want_mut || matches!(m, rustc_hir::Mutability::Mut)
                        ) =>
                        {
                            return ReborrowTarget::Ptr(inner);
                        }
                        _ => return ReborrowTarget::NotAPlace,
                    }
                }
                _ => return ReborrowTarget::NotAPlace,
            }
        }
    }

    /// Trust: peel a slice-typed reborrow expression down to the slice VALUE producer. A `&[T]`
    /// receiver formed by auto-reborrow is `Borrow{Shared, Deref{<slice>}}` — borrowing the deref of a
    /// slice value is the slice value itself — so we strip `Scope`/`Use` and that `Borrow{Deref{..}}`
    /// pair, returning the inner slice expr (e.g. the `VarRef(s)` of a slice local). Any non-reborrow
    /// shape is returned unchanged for the caller to lower directly.
    fn slice_value_expr(&self, mut e: ExprId) -> ExprId {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Borrow {
                    borrow_kind:
                        rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_),
                    arg,
                } => {
                    // Only peel a `Borrow{Shared, Deref{..}}` reborrow (the deref's inner is the slice
                    // value). A borrow of a non-deref place is left for the caller.
                    let mut inner = *arg;
                    loop {
                        match &self.thir.exprs[inner].kind {
                            ExprKind::Scope { value, .. } => inner = *value,
                            ExprKind::Use { source } => inner = *source,
                            _ => break,
                        }
                    }
                    match &self.thir.exprs[inner].kind {
                        ExprKind::Deref { arg: slice } => e = *slice,
                        _ => return e,
                    }
                }
                _ => return e,
            }
        }
    }

    /// Trust: recognize the `&a[..]` full-range slice shape and return the underlying array PLACE.
    /// `arg` is the borrow operand of `&a[..]`, which rustc lowers as
    /// `Deref{ Call{ <[T] as Index<RangeFull>>::index, [ &a_array, RangeFull ] } }` — the deref of the
    /// `Index::index` result place. We confirm:
    ///   * the (peeled) `arg` is a `Deref` whose inner expr is a `Call`;
    ///   * the call has exactly two args and the SECOND arg's type is `RangeFull` (the full range);
    ///   * the FIRST arg peels to an array place (`array_place_expr` bottoms out at a `[T; N]` local).
    /// Returns the array place `ExprId` (its `.ty` is `[T; N]`), or `None` for any other index shape
    /// (a sub-range `a[1..3]`, a `Vec`, an overloaded user `Index`, a non-array base).
    fn full_range_slice_array(&self, mut arg: ExprId) -> Option<ExprId> {
        loop {
            match &self.thir.exprs[arg].kind {
                ExprKind::Scope { value, .. } => arg = *value,
                ExprKind::Use { source } => arg = *source,
                ExprKind::Deref { arg: inner } => {
                    arg = *inner;
                    break;
                }
                _ => return None,
            }
        }
        // `arg` is now the `Index::index` call (peel Scope/Use first).
        loop {
            match &self.thir.exprs[arg].kind {
                ExprKind::Scope { value, .. } => arg = *value,
                ExprKind::Use { source } => arg = *source,
                _ => break,
            }
        }
        let (base_arg, range_arg) = match &self.thir.exprs[arg].kind {
            ExprKind::Call { args, .. } if args.len() == 2 => (args[0], args[1]),
            _ => return None,
        };
        // The second arg must be a `RangeFull` (the `..` full range). RangeFull is a unit struct in
        // `core::ops::range`; match it by the diagnostic item on its ADT.
        let range_rty = self.thir.exprs[range_arg].ty;
        let is_full_range = match range_rty.kind() {
            ty::Adt(adt, _) => self.tcx.lang_items().range_full_struct() == Some(adt.did()),
            _ => false,
        };
        if !is_full_range {
            return None;
        }
        // The first arg (`&a`) must peel to an array place.
        self.array_place_expr(base_arg)
    }

    /// Trust: peel an array-to-slice coercion source down to the underlying array PLACE expression.
    /// rustc wraps an array place in an autoref/autoderef chain when forming `&[T; N]` for the unsize
    /// coercion — e.g. `Borrow{Shared, Deref{Borrow{Shared, VarRef(a)}}}`. We strip `Scope`/`Use` and
    /// any `Borrow{Shared|Fake}` / `Deref` layers (a borrow-then-deref of a place is the place itself)
    /// and return the inner `ExprId` once it is a bare `VarRef` place. Returns `None` for any other
    /// shape (a non-local array place, an `&mut` layer, an array literal not bound to a local). The
    /// returned expr's `.ty` is the array's rustc type and `place_local` yields its `LocalVarId`.
    fn array_place_expr(&self, mut place: ExprId) -> Option<ExprId> {
        loop {
            match &self.thir.exprs[place].kind {
                ExprKind::Scope { value, .. } => place = *value,
                ExprKind::Use { source } => place = *source,
                ExprKind::Borrow {
                    borrow_kind:
                        rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_),
                    arg,
                } => place = *arg,
                ExprKind::Deref { arg } => place = *arg,
                ExprKind::VarRef { .. } => return Some(place),
                _ => return None,
            }
        }
    }

    /// Trust: if `place` is a `*r` DEREF place (peeling `Scope`/`Use` wrappers), return the `arg`
    /// `ExprId` of the inner `ExprKind::Deref` — the pointer being written through in `*r = v`.
    /// `None` for any non-deref place (a bare local, field/index projection). The caller checks the
    /// lowered `arg` is a known `&mut` borrow pointer before emitting the `Store`.
    fn deref_place_arg(&self, mut place: ExprId) -> Option<ExprId> {
        loop {
            match &self.thir.exprs[place].kind {
                ExprKind::Scope { value, .. } => place = *value,
                ExprKind::Use { source } => place = *source,
                ExprKind::Deref { arg } => return Some(*arg),
                _ => return None,
            }
        }
    }

    /// Trust (wave-CB): does the borrow arg peel (`Scope`/`Use`) to a NAMED const / const-block —
    /// a pure const VALUE with no runtime place? rustc materializes such a borrow in a STACK
    /// temporary (`_2 = const K; _1 = &_2`), so it is faithfully snapshot-able (see the `Borrow`
    /// arm's local-const branch). Distinguishes it from a runtime place (`&param.field`, an
    /// `ExprKind::Field` — NOT a const, must stay fail-closed) and from a literal / promotable
    /// const-expr (already `'static`-promoted by `eval_promotable_scalar`).
    fn is_const_borrow_arg(&self, mut e: ExprId) -> bool {
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::NamedConst { .. } | ExprKind::ConstBlock { .. } => return true,
                _ => return false,
            }
        }
    }

    /// Trust (wave-23, ref-escape memory model): recognize a `(*p).field` PLACE — a
    /// `Field{ lhs: Deref{ arg }, name }` after peeling `Scope`/`Use` on both levels. Returns
    /// `(ptr_expr, deref_expr, field_idx)`:
    ///
    ///   * `ptr_expr` = the deref's `arg` — the caller lowers it and requires a `&mut` slot ptr
    ///     (`is_mut_borrow_ptr`), i.e. a `&mut Struct` param registered by the param pre-pass.
    ///   * `deref_expr` = the `*p` expr — its `.ty` is the WHOLE-struct pointee type, typing the
    ///     `Load`/`Store` (`map_ty` must yield a registered `Ty::Struct(id)`).
    ///   * `field_idx` = the THIR `FieldIdx` (declaration order — the SAME index the `Field` read
    ///     arm's `ExtractField` and the struct-construction `InsertField` use).
    ///
    /// `None` for every other place (a bare local, a bare `*r`, a nested `a.b.c`, an `Index`, an
    /// enum-variant downcast) — the caller keeps its precise fail-closed tag. This is intentionally
    /// SHALLOW (exactly one `Field` over exactly one `Deref`): the nested `a.b.c` chain is
    /// wave-31's `field_chain_deref_place`, to which this delegates (length-1 filter — provably
    /// the pre-wave-31 behavior: the chain walker returns the same `(ptr, deref, idx)` for the
    /// one-level shape and a longer chain for exactly the shapes this returned `None` on).
    fn field_deref_place(&self, place: ExprId) -> Option<(ExprId, ExprId, u32)> {
        match self.field_chain_deref_place(place) {
            Some((ptr_expr, deref_expr, chain)) if chain.len() == 1 => {
                Some((ptr_expr, deref_expr, chain[0].1))
            }
            _ => None,
        }
    }

    /// Trust (wave-31, NESTED-place assign): recognize a `(*p).f1.f2.….fk` PLACE — a CHAIN of
    /// `Field` projections bottoming out at a single `Deref`, peeling `Scope`/`Use` at every
    /// level (and the top-level `Deref{Borrow{place}}` reborrow wrapper, exactly as the wave-25
    /// one-level recognizer did). Returns `(ptr_expr, deref_expr, chain)`:
    ///
    ///   * `ptr_expr` = the bottom deref's `arg` — the caller lowers it and requires a `&mut`
    ///     slot ptr (`is_mut_borrow_ptr`), i.e. a `&mut Struct` param registered by the pre-pass.
    ///   * `deref_expr` = the `*p` expr — its `.ty` is the ROOT pointee type, typing the
    ///     whole-struct `Load`/`Store`.
    ///   * `chain` = the field path in ROOT-FIRST order: `chain[0]` projects the pointee,
    ///     `chain.last()` is the assigned leaf. Each element is `(field_expr, field_idx)`;
    ///     `field_expr.ty` is the PROJECTED value's type (an intermediate link's ty is the
    ///     nested aggregate, the leaf's ty is the stored scalar), `field_idx` the THIR
    ///     `FieldIdx` (declaration order — the same index `ExtractField`/`InsertField` use).
    ///
    /// `chain.len() == 1` is exactly the wave-23 `(*p).field` shape. `None` for anything else
    /// along the chain (`Index`, enum downcast, a mid-chain deref, a bare `*r`/local): callers
    /// keep their precise fail-closed tags. Termination: THIR is a tree and every step descends
    /// into a strict subexpression.
    fn field_chain_deref_place(
        &self,
        mut place: ExprId,
    ) -> Option<(ExprId, ExprId, Vec<(ExprId, u32)>)> {
        // Collected leaf-first while walking outside-in; reversed to root-first on success.
        let mut rev_chain: Vec<(ExprId, u32)> = Vec::new();
        loop {
            match &self.thir.exprs[place].kind {
                ExprKind::Scope { value, .. } => place = *value,
                ExprKind::Use { source } => place = *source,
                // Trust (wave-25): peel the `Deref{Borrow{place}}` reborrow wrapper THIR puts around
                // a borrowed place — `&s.field` lowers to `Borrow{Deref{Borrow{Field{Deref{..}}}}}`
                // (`&*&(s.field)`), so the Borrow arm's `arg` starts with this wrapper. `*&place ==
                // place`, so peel to the inner place and continue. NO-OP for the write arms (an
                // assignment lhs `(*p).f…` is a bare `Field{…{Deref{..}}}`, never Deref-wrapped;
                // a `*p` deref-of-non-Borrow returns `None` exactly as before).
                ExprKind::Deref { arg } => {
                    let mut inner = *arg;
                    loop {
                        match &self.thir.exprs[inner].kind {
                            ExprKind::Scope { value, .. } => inner = *value,
                            ExprKind::Use { source } => inner = *source,
                            _ => break,
                        }
                    }
                    if let ExprKind::Borrow { arg: reborrowed, .. } = &self.thir.exprs[inner].kind {
                        place = *reborrowed;
                    } else {
                        return None;
                    }
                }
                ExprKind::Field { lhs, name, .. } => {
                    rev_chain.push((place, name.as_u32()));
                    let mut inner = *lhs;
                    loop {
                        match &self.thir.exprs[inner].kind {
                            ExprKind::Scope { value, .. } => inner = *value,
                            ExprKind::Use { source } => inner = *source,
                            _ => break,
                        }
                    }
                    match &self.thir.exprs[inner].kind {
                        // Bottomed out at the deref of the base pointer: done.
                        ExprKind::Deref { arg } => {
                            rev_chain.reverse();
                            return Some((*arg, inner, rev_chain));
                        }
                        // A deeper field link: keep walking (the next iteration pushes it).
                        ExprKind::Field { .. } => place = inner,
                        // Index / downcast / local-rooted (`s.a.b` on a bare local) / anything
                        // else: not this shape — fail closed at the caller.
                        _ => return None,
                    }
                }
                _ => return None,
            }
        }
    }

    /// Trust (wave-25b): the BYTE OFFSET of `field` (source/declaration index) within struct
    /// `struct_rty`, or `None` when it cannot be determined faithfully. A SINGLE-FIELD struct's sole
    /// field is unconditionally at offset 0 (nothing to reorder, structs carry no leading padding) —
    /// holds even for a GENERIC struct, needing no layout. A multi-field struct needs a CONCRETE
    /// layout: unresolved inputs are rejected before `layout_of` because this runs inside
    /// `mir_built`, where normalization can query-cycle rather than return an error. The offset
    /// is READ ONLY from rustc's authoritative `layout.fields.offset` (source-declaration indexed,
    /// reordering-aware) — never hand-computed. The `&self.field` interior-borrow-return recognizer
    /// returns the base ptr verbatim on `Some(0)` (wave-25 tautology) and emits a flat-I8 `GEP` of
    /// this offset otherwise (wave-25b).
    fn field_byte_offset(&self, struct_rty: RustcTy<'tcx>, field: u32) -> Option<u64> {
        let ty::Adt(adt, _) = struct_rty.kind() else {
            return None;
        };
        if !adt.is_struct() {
            return None;
        }
        let nfields = adt.non_enum_variant().fields.len();
        if field as usize >= nfields {
            return None;
        }
        if nfields == 1 {
            return Some(0);
        }
        if !layout_query_is_reentrant_safe(struct_rty) {
            return None;
        }
        let te = ty::TypingEnv::fully_monomorphized();
        let layout = cycle_safe_layout_of(self.tcx, te, struct_rty)?;
        // `FieldsShape::offset` panics out of range; a layout can carry fewer
        // field entries than the ADT declares. Decline, never abort.
        if field as usize >= layout.fields.count() {
            return None;
        }
        Some(layout.fields.offset(field as usize).bytes())
    }

    /// Trust (wave-DP): is the body CURRENTLY being lowered a `Deref::deref` /
    /// `DerefMut::deref_mut` impl method? Gates the accessor-body interior-`&mut`-return lane:
    /// only inside such an accessor may `&mut (*self).fieldK` lower (witness + interior GEP)
    /// instead of failing closed — the emitted body is the PROJECTION WITNESS a downstream
    /// deref-resolution pass verifies before folding a deref-chain write into a nested place.
    fn body_is_deref_accessor(&self) -> bool {
        let Some(impl_did) = self.tcx.impl_of_assoc(self.body_def) else { return false };
        let Some(t) = self.tcx.impl_opt_trait_id(impl_did) else { return false };
        let li = self.tcx.lang_items();
        Some(t) == li.deref_trait() || Some(t) == li.deref_mut_trait()
    }

    /// Trust (wave-DP, deref-projection): `&mut (*self).fieldK` inside a `Deref`/`DerefMut`
    /// ACCESSOR body — the canonical `fn deref_mut(&mut self) -> &mut Target { &mut self.fieldK }`
    /// shape (the real `GridStorage → GridCursorState → GridPresentationState` chain). Lowers as:
    ///
    ///   %w0 = Load  { ty: <registered self struct>, ptr: %self }   ; PROJECTION WITNESS
    ///   %w1 = ExtractField { ty: <registered field ty>, %w0, K }   ; carries K structurally
    ///   ret %self                        (field byte offset 0 — wave-25 tautology)
    ///   —or— %p = GEP i8 %self + offset; ret %p                    (wave-25b interior ptr)
    ///
    /// The Load/ExtractField pair is DEAD CODE for execution but STRUCTURALLY LOAD-BEARING: it
    /// carries the projected FIELD INDEX `K` (and the registered source/target struct ids) into
    /// the emitted IR, which a byte-offset GEP alone cannot (layout reordering is not invertible
    /// from the dump). A downstream temporal extractor VERIFIES this exact body shape before
    /// trusting the accessor as a pure field projection and folding caller-side deref-chain
    /// writes (`lower_deref_mut_chain_ptr`) into nested place paths. The compiler itself never
    /// assumes deref == projection at any CALL site (other bodies' THIR is stolen); only HERE,
    /// lowering the accessor's OWN body, is K known exactly.
    ///
    /// FAIL-CLOSED (`None` ⇒ the caller keeps `Borrow(&mut non-local place)`): not a
    /// deref-accessor body; not a one-level `(*self).field` place; a non-struct pointee or a
    /// generic multi-field layout (`field_byte_offset` `None`); an unregistrable self struct or
    /// a projected lane that is not itself a registered `Ty::Struct` holder (the chain fold only
    /// steps through struct lanes); a fat/DST target ref; a base that is not the `&mut self`
    /// receiver param. Mirrors wave-25b's ledger discipline: the derived interior ptr enters
    /// `borrow_ptrs` (every non-return escape fails closed) + `interior_ptrs` (return-admitted).
    /// The differential stays CLEAN-ONLY (the MIR side lowers the accessor differently → NotRun;
    /// these bodies were previously DECLINED outright, so this is strictly new clean coverage).
    fn try_lower_deref_accessor_interior_mut(
        &mut self,
        _expr_span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        arg: ExprId,
    ) -> Option<ValueId> {
        if !self.body_is_deref_accessor() {
            return None;
        }
        let (ptr_expr, deref_expr, field) = self.field_deref_place(arg)?;
        let struct_rty = self.thir.exprs[deref_expr].ty;
        let (adt, gargs) = match struct_rty.kind() {
            ty::Adt(adt, gargs) if adt.is_struct() => (*adt, *gargs),
            _ => return None,
        };
        // The borrow result must be a THIN `&mut Target` mapping to a real `Ty::Ptr` (same
        // gates as the wave-25b shared interior return).
        if self.fat_shape(expr_ty, &mut Vec::new()) != FatShape::Thin
            || !matches!(self.map_ty(expr_ty), Ty::Ptr)
        {
            return None;
        }
        let off = self.field_byte_offset(struct_rty, field)?;
        let struct_ty = self.struct_ty_rmw_opaque(adt, gargs, None)?;
        let Ty::Struct(sid) = struct_ty.clone() else { return None };
        let leaf_ty = self.registered_struct_field_tys(sid)?.get(field as usize)?.clone();
        // The projected lane must be a registered STRUCT holder — the deref-projection fold
        // steps only through struct lanes (an opaque/scalar Target is not a foldable hop).
        if !matches!(leaf_ty, Ty::Struct(_)) {
            return None;
        }
        let mark = self.unsupported.len();
        let pv = match self.lower_expr(ptr_expr) {
            Some(p) => p,
            None => {
                self.unsupported.truncate(mark);
                return None;
            }
        };
        // The base must be the `&mut self` receiver param: caller memory that outlives the
        // call (return-faithful), registered mutable (a writable projection).
        if !(self.ref_param_ptrs.contains(&pv) && self.is_mut_borrow_ptr(pv)) {
            return None;
        }
        // THE PROJECTION WITNESS (dead for execution; carries K + the struct ids).
        let w0 = self.fresh();
        self.push_node(InstrNode::new(Inst::Load { ty: struct_ty, ptr: pv, volatile: false, align: None })
                .with_result(w0),
        );
        let w1 = self.fresh();
        self.push_node(InstrNode::new(Inst::ExtractField { ty: leaf_ty, aggregate: w0, field })
                .with_result(w1),
        );
        if off == 0 {
            // The field address IS the struct pointer (wave-25 tautology).
            return Some(pv);
        }
        let off_val = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(off as i128) })
                .with_result(off_val),
        );
        let iptr = self.fresh();
        self.push_node(InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: pv,
                indices: vec![off_val],
                inbounds: true,
            })
            .with_result(iptr),
        );
        self.borrow_ptrs.push(iptr);
        self.interior_ptrs.push(iptr);
        // ALSO the mut ledger: THIR may wrap the accessor's tail in a mut REBORROW
        // (`Borrow{Mut, Deref{Borrow{Mut, Field}}}`), whose outer hop returns the
        // inner pointer only `if is_mut_borrow_ptr(v)` — and this IS a `&mut`
        // interior pointer (writes through it inside the accessor body would be
        // pathological but sound to Store; the extractor's strict shape check
        // rejects any such body at fold time).
        self.mut_borrow_ptrs.push(iptr);
        Some(iptr)
    }

    /// Trust (wave-DP, deref-projection): recognize + lower the POINTER of a nested-field
    /// ASSIGN place whose bottom pointer is an AUTO-DEREF-MUT CALL CHAIN — the
    /// `self.storage.damage = Damage::Full;` shape, whose THIR is
    ///
    ///   Field(damage) over Deref{ Call(<GridCursorState as DerefMut>::deref_mut,
    ///     [&mut Deref{ Call(<GridStorage as DerefMut>::deref_mut, [&mut (*self).storage]) }]) }
    ///
    /// Each hop lowers as an OPAQUE `call @<Impl as DerefMut>::deref_mut(<receiver>)` — the
    /// wave-MC place-path-carrier pattern: the INNERMOST receiver is the nested field place's
    /// leaf VALUE (`Load` root + `ExtractField` chain — the same opaque-tolerant read machinery
    /// `self.storage.<field>` uses), and each outer hop's receiver is the previous hop's call
    /// RESULT. The final result registers in `mut_borrow_ptrs` (+ `borrow_ptrs`, so every other
    /// escape fails closed) so the chain-assign arm's `is_mut_borrow_ptr` admits it as the
    /// through-pointer of the structured deref-write (whole-struct `Load`/`InsertField`/`Store`
    /// through the chain result — the pointee type is the final `Deref` expr's own type, i.e.
    /// the LAST hop's Target).
    ///
    /// STRUCTURE WITHOUT SEMANTICS: no deref impl is assumed to be a field projection here —
    /// the emitted IR only CARRIES the callee chain + receiver place. A downstream extractor
    /// must verify each callee's own lowered accessor body (the projection WITNESS emitted by
    /// `try_lower_deref_accessor_interior_mut`) before folding; the emitted calls set
    /// `contains_call` (structurally NotRun — never interpreted/flipped, CLEAN-ONLY).
    ///
    /// FAIL-CLOSED (`None` ⇒ caller falls through to the pre-wave path and its precise tags):
    /// any hop that is not a `from_hir_call == false` call to the `DerefMut::deref_mut` trait
    /// method with exactly one `&mut` arg; a bottom receiver that is not a resolvable nested
    /// FIELD place (`field_chain_deref_place`); an unresolvable/indirect callee; a receiver
    /// place whose leaf value cannot lower. A raw-pointer write, a method call through the
    /// chain, or a shared-deref read all keep their existing fail-closed tags.
    fn lower_deref_mut_chain_ptr(&mut self, e: ExprId) -> Option<ValueId> {
        // ---- Phase 1: RECOGNIZE (pure — no emission, no tags). Hops collected
        // OUTERMOST-first; `fun` operands kept for callee resolution.
        let mut hops: Vec<ExprId> = Vec::new();
        let mut cur = e;
        let base_place: ExprId = loop {
            loop {
                match &self.thir.exprs[cur].kind {
                    ExprKind::Scope { value, .. } => cur = *value,
                    ExprKind::Use { source } => cur = *source,
                    _ => break,
                }
            }
            let ExprKind::Call { fun, args, from_hir_call: false, .. } = &self.thir.exprs[cur].kind
            else {
                return None;
            };
            let fun = *fun;
            let ty::FnDef(fdid, _) = self.thir.exprs[fun].ty.kind() else { return None };
            // The auto-deref adjustment call names the `DerefMut::deref_mut` TRAIT method.
            if self.tcx.trait_of_assoc(*fdid) != self.tcx.lang_items().deref_mut_trait() {
                return None;
            }
            if args.len() != 1 {
                return None;
            }
            let mut a = args[0];
            loop {
                match &self.thir.exprs[a].kind {
                    ExprKind::Scope { value, .. } => a = *value,
                    ExprKind::Use { source } => a = *source,
                    _ => break,
                }
            }
            let ExprKind::Borrow {
                borrow_kind: rustc_middle::mir::BorrowKind::Mut { .. },
                arg: place,
            } = &self.thir.exprs[a].kind
            else {
                return None;
            };
            let mut p = *place;
            loop {
                match &self.thir.exprs[p].kind {
                    ExprKind::Scope { value, .. } => p = *value,
                    ExprKind::Use { source } => p = *source,
                    _ => break,
                }
            }
            hops.push(fun);
            match &self.thir.exprs[p].kind {
                // `&mut *<inner deref_mut(..)>` — the next (inner) hop; keep walking.
                ExprKind::Deref { arg: inner } => cur = *inner,
                // Bottom: a resolvable NESTED FIELD place (the wave-MC carrier shape).
                _ if self.field_chain_deref_place(p).is_some() => break p,
                _ => return None,
            }
        };
        // ---- Phase 2: RESOLVE every hop callee BEFORE emitting anything (a later
        // failure must not leave dead calls; a stale admit ledger entry is harmless —
        // and unreachable for the shapes that get here, since resolution of a concrete
        // `DerefMut` impl method only fails on generics, which the receiver-place gate
        // already excludes in practice).
        let mut callees: Vec<FuncId> = Vec::with_capacity(hops.len());
        for &fun in hops.iter().rev() {
            match self.resolve_callee(fun, false) {
                Ok(CalleeKind::Direct(c)) => callees.push(c),
                _ => return None,
            }
        }
        // ---- Phase 3: EMIT. The innermost receiver = the field place's leaf VALUE.
        let mark = self.unsupported.len();
        let recv = match self.lower_expr(base_place) {
            Some(v) => v,
            None => {
                // Undo this attempt's tags: the caller's fallback re-lowers the original
                // ptr expr and produces the canonical pre-wave tags.
                self.unsupported.truncate(mark);
                return None;
            }
        };
        // The carrier must be a place VALUE, never a pointer.
        if self.is_borrow_ptr(recv) {
            return None;
        }
        let mut val = recv;
        for &callee in &callees {
            let res = self.fresh();
            self.contains_call = true;
            self.push_node(InstrNode::new(Inst::Call { callee, args: vec![val] }).with_result(res));
            val = res;
        }
        // The chain result is the write-through pointer: admit it in the mut ledger (the
        // chain-assign arm checks `is_mut_borrow_ptr`) and the general borrow ledger (every
        // OTHER escape of it stays fail-closed).
        self.mut_borrow_ptrs.push(val);
        if !self.borrow_ptrs.contains(&val) {
            self.borrow_ptrs.push(val);
        }
        Some(val)
    }

    /// Trust: true iff `v` is a borrow-produced `Ty::Ptr` (recorded by the `ExprKind::Borrow` arm).
    /// Value-consuming sites use this to fail closed if such a pointer would ESCAPE the only
    /// supported shape — a `Deref` immediately consuming it. See the `borrow_ptrs` field. A `&mut`
    /// slot pointer is registered into `borrow_ptrs` too, so the same escape guards cover it.
    fn is_borrow_ptr(&self, v: ValueId) -> bool {
        self.borrow_ptrs.contains(&v)
    }

    /// Trust: true iff `v` is a `&mut`-produced slot pointer (from `ExprKind::Borrow{Mut}`). The
    /// `*r = v` write arm uses this to recognize a writable target; a `Deref` read accepts it too.
    fn is_mut_borrow_ptr(&self, v: ValueId) -> bool {
        self.mut_borrow_ptrs.contains(&v)
    }

    /// Trust: true iff `var` is a memory-PROMOTED local (it is `&mut`-borrowed somewhere — the
    /// pre-pass put it in `promoted`). Reads/writes/`&mut` of such a local route to `Load`/`Store`/
    /// the slot Ptr instead of the SSA `locals` map.
    fn is_promoted(&self, var: LocalVarId) -> bool {
        self.promoted.contains(&var)
    }

    /// Trust: the slot `ValueId` (a `Ty::Ptr`) backing a promoted local, if its `Alloca` has been
    /// emitted (at the local's `let`/param). `None` before declaration (a use-before-`let` would be a
    /// type error rustc already rejects; defensive callers fail closed).
    fn promoted_slot(&self, var: LocalVarId) -> Option<ValueId> {
        self.promoted_slots.iter().find(|(v, _)| *v == var).map(|(_, p)| *p)
    }

    /// Trust: the (interpretable scalar) pointee `Ty` of a promoted local's slot.
    fn promoted_ty(&self, var: LocalVarId) -> Option<Ty> {
        self.promoted_tys.iter().find(|(v, _)| *v == var).map(|(_, t)| t.clone())
    }

    /// Trust: emit the `Alloca` slot for a promoted local `var` of (scalar) type `ty` and `Store` its
    /// initial value, recording the slot in `promoted_slots`/`promoted_tys`. Idempotent: re-declaring
    /// (a shadowing `let` of the SAME LocalVarId never happens — each `let` mints a fresh var — so the
    /// `is_some` guard only protects against a defensive double call). Returns the slot `ValueId`.
    fn alloc_promoted(&mut self, var: LocalVarId, ty: Ty, init: ValueId) {
        if self.promoted_slot(var).is_some() {
            // Slot already exists: just (re)store the new initial value into it.
            if let Some(slot) = self.promoted_slot(var) {
                self.push_node(InstrNode::new(Inst::Store {
                    ty,
                    ptr: slot,
                    value: init,
                    volatile: false,
                    align: None,
                }));
            }
            return;
        }
        let slot = self.fresh();
        self.push_node(InstrNode::new(Inst::Alloca { ty: ty.clone(), count: None, align: None })
                .with_result(slot),
        );
        self.push_node(InstrNode::new(Inst::Store {
            ty: ty.clone(),
            ptr: slot,
            value: init,
            volatile: false,
            align: None,
        }));
        self.promoted_slots.push((var, slot));
        self.promoted_tys.push((var, ty));
    }

    /// Build the (possibly multi-block) `trust_ir::Function` and push it onto the module.
    fn lower_fn(
        &mut self,
        module: &mut Module,
        def: LocalDefId,
        fn_sig: ty::FnSig<'tcx>,
        body: ExprId,
    ) {
        // Trust: record the declared return type for the `?`-operator lowering (`lower_try_question`),
        // which needs it to synthesize the early-return `Err(e)`/`None` value.
        self.fn_return_rty = Some(fn_sig.output());
        // Trust: match the MIR-side bridge's signature convention — a unit-returning fn has
        // `returns: []` (not `[Ty::Unit]`) and its `Inst::Return` carries no values. The
        // `[Unit]` spelling was the single largest differential-divergence class (every
        // 'signature divergence: THIR []->[Unit] vs MIR []->[]' verdict — 890 bodies in the
        // 2026-07-01 ui-sample scorecard), masking any real semantic comparison on unit fns.
        let returns =
            if fn_sig.output().is_unit() { Vec::new() } else { vec![self.map_ty(fn_sig.output())] };
        // Trust: closure-environment signature convention — a closure BODY's param 0 is the
        // closure environment, then the declared params. THIR already carries the env as
        // `thir.params[0]` (pat `None`; see `rustc_mir_build::thir::cx::closure_env_param`,
        // which prepends `closure_env_ty` — `&{closure}` for `Fn`, `&mut {closure}` for
        // `FnMut`, the closure type by value for `FnOnce`), and MIR builds the env as `_1`,
        // so the MIR-side oracle (`trust_mir_extract` → `trust_ir_bridge`) signs closure
        // bodies as `[Ptr, declared…]` / `[Unit, declared…]`. The producer's `fn_sig` is the
        // *liberated* closure sig (declared inputs only, no env — typeck's
        // `liberated_fn_sigs`), so deriving `params` from `fn_sig.inputs()` alone dropped the
        // env: every closure body diverged as 'signature divergence: THIR []->[] vs MIR
        // [Ptr]->[]' (~4150 of 4183 divergences in the 2026-07-01 postbuild-unitret
        // scorecard) AND mis-aligned `param_vars` below (THIR param index `i` no longer
        // matched `params[i]`/`ValueId(i)`, so a declared closure param bound to a
        // NON-EXISTENT value id that the first `fresh()` then re-minted). Prepending the env
        // ty restores both: the env gets block-param position 0 (`ValueId(0)`; its pat is
        // `None`, so `param_vars` never binds it) and declared params re-align at `i ≥ 1`.
        // Coroutine / by-value-capturing conventions the oracle signs differently are
        // fail-closed with precise tags in `closure_env_param_ty` — never guessed.
        let mut params: Vec<Ty> = Vec::with_capacity(fn_sig.inputs().len() + 1);
        params.extend(self.closure_env_param_ty(def));
        params.extend(fn_sig.inputs().iter().map(|t| self.map_ty(*t)));
        // Trust: a C-variadic body's THIR carries a trailing implicit `VaList` param that is
        // NOT in `fn_sig.inputs()` (see `rustc_hir_typeck::check::check_fn`), which would
        // mis-align `param_vars` exactly like the closure-env case above. Fail closed.
        // Trust: rust 1.99 — `FnSig.c_variadic` is now an accessor method, not a field.
        if fn_sig.c_variadic() {
            self.unsupported.push(("body".to_string(), "c-variadic body (VaList param)"));
        }
        let func_ty_id =
            module.add_func_type(FuncTy { params: params.clone(), returns, is_vararg: false });

        let entry = BlockId::new(0);
        // Open the entry block with its signature params as block params.
        let entry_params: Vec<(ValueId, Ty)> =
            params.iter().enumerate().map(|(i, p)| (ValueId::new(i as u32), p.clone())).collect();
        self.start_block(entry, entry_params);
        self.next_value = params.len() as u32;

        // Seed the binding environment: each param pattern var → its block-param value.
        // Trust: the rustc param type rides along (wave-5) so ref-typed params can be
        // ledger-registered below — `self.thir.params[i].ty` is the param's ACTUAL type
        // (correct for closure bodies too, where `fn_sig` is the liberated sig).
        let param_vars: Vec<(usize, LocalVarId, RustcTy<'tcx>)> = self
            .thir
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                p.pat.as_ref().and_then(|pat| binding_var(pat)).map(|v| (i, v, p.ty))
            })
            .collect();
        // Trust (C2-names): record each named param on the Module — entry param i IS
        // ValueId(i) (the `entry_params` construction above), so index alignment is by
        // construction, not by bookkeeping. A pattern without a plain binding (closure env,
        // destructured param) simply contributes no name.
        for (i, p) in self.thir.params.iter().enumerate() {
            if let Some(name) = p.pat.as_ref().and_then(|pat| binding_name(pat)) {
                self.value_names.push((ValueId::new(i as u32), name.to_string()));
            }
        }
        // Trust: pre-pass — collect every local `&mut`-borrowed anywhere in the body. Such a local is
        // PROMOTED to a memory slot for its whole lifetime (Alloca + Load/Store), because a write
        // through the pointer (`*r = v`) must be visible to later reads — SSA value-versioning cannot
        // express that. A promoted local is never `set_local`'d, so it is automatically excluded from
        // every SSA block-param merge (the memory slot is its single source of truth). We only promote
        // SCALAR locals (the slot Load/Store round-trips a scalar); a `&mut` of a non-scalar local
        // fails closed at the `Borrow{Mut}` arm. Pointer-flavored types (a `&mut` of a reference) are
        // likewise excluded so we never promote a slot whose value is itself a pointer.
        self.promoted = self.collect_mut_borrowed(body);

        for (i, var, rty) in param_vars {
            // The param's `Ty` is `params[i]` (the mapped sig type).
            let ty = params.get(i).cloned().unwrap_or(Ty::Unit);
            if self.is_promoted(var) {
                // A `&mut`-borrowed PARAMETER: promote it at entry — Alloca a slot, Store the incoming
                // param value. Only scalars are promotable; a non-scalar promoted param fails closed
                // (its `&mut` site would too, but guard here so we never emit a non-scalar slot).
                if is_scalar_ty(&ty) {
                    self.alloc_promoted(var, ty, ValueId::new(i as u32));
                } else {
                    self.unsupported.push(("param".to_string(), "Promote(non-scalar &mut param)"));
                }
            } else {
                // Record the param's `Ty` too, so a `mut` param reassigned inside an `if`/`match` arm
                // can be typed at its join block-param.
                self.set_local(var, ValueId::new(i as u32), ty.clone());
                // Trust: wave-5 — a REF-TYPED param (`&T` / `&mut T`, T a MODELED scalar) is the
                // CALLER's slot pointer: its pointee is accessed via exactly the promoted-slot
                // memory model (`Load`/`Store` through a `Ty::Ptr`), except the slot lives in the
                // caller's frame. Register the param's ValueId in the SAME ledgers the local
                // borrow machinery uses, so `*r` → `Load` (Deref arm), `*r = v` / `*r += v` →
                // `Store` (Assign/AssignOp arms), and reborrow forwarding (`g(r)`, `&*r`) work
                // unchanged. A SHARED ref enters `borrow_ptrs` only, so the mut ledger keeps it
                // Load-only (`*r = v` through `&T` is borrowck-rejected anyway); `&mut` enters
                // both. Gates, all fail-closed elsewhere if not met:
                //   * pointee must be a modeled scalar (bool / fixed-width or ptr-width int —
                //     exactly the set the Deref/Assign arms accept via `is_scalar_ty`): `&&T`,
                //     `&f64`, `&str`, `&Struct` params stay UNREGISTERED opaque values (their
                //     derefs keep the precise `Deref(non-borrow ptr)`/pointee tags, and their
                //     pass-through uses stay outside the ledger escape guards).
                //   * the mapped sig type must actually be `Ty::Ptr` (belt-and-braces against a
                //     future `map_ty` widening; `&[T]` maps to the fat tuple, not `Ptr`).
                // Ledger membership also subjects the param ptr to the EXISTING escape guards
                // (return / aggregate / binop sites) — fail-closed, and faithful-by-refusal:
                // those sites never spliced a param ptr before either (it was opaque).
                // Interpreter differential: a READ ref param trips `param_never_read` → the body
                // stays NotRun (unsampleable — documented); the derived-MIR shim fails closed at
                // the Load/Store slot lookup with a precise ref-param reason (to_mir.rs).
                if matches!(ty, Ty::Ptr) {
                    if let ty::Ref(_, pointee, mutbl) = rty.kind() {
                        let scalar_pointee =
                            matches!(pointee.kind(), ty::Bool | ty::Int(_) | ty::Uint(_));
                        let pv = ValueId::new(i as u32);
                        // Trust (wave-14): mark a REGISTERED ref-param ptr as ref-PARAM-origin (a
                        // subset of `borrow_ptrs`) so the return-escape guards may admit returning it
                        // (it outlives the call); every non-param borrow-ptr (a `&local` snapshot)
                        // stays out of this set and fail-closed.
                        if scalar_pointee {
                            if !self.borrow_ptrs.contains(&pv) {
                                self.borrow_ptrs.push(pv);
                            }
                            if mutbl.is_mut() && !self.mut_borrow_ptrs.contains(&pv) {
                                self.mut_borrow_ptrs.push(pv);
                            }
                            if !self.ref_param_ptrs.contains(&pv) {
                                self.ref_param_ptrs.push(pv);
                            }
                        } else if mutbl.is_not() {
                            // Trust (wave-8a): a NON-scalar SHARED ref param (`&Struct`, the
                            // `&self` receiver on a struct method, `&[T]`-less aggregate refs).
                            // Register it in `borrow_ptrs` (Load ledger) SOLELY so FORWARDING
                            // resolves it: `g(s)` / `&*s` / the `s.method()` receiver reborrow
                            // (`Borrow{Shared, Deref{VarRef(s)}}` → `reborrow_target` Ptr → this
                            // pv) passes the pointer through unchanged. Every OTHER use stays
                            // fail-closed: `*s` hits the Deref arm's scalar-pointee gate
                            // (`Deref(non-scalar pointee)`), and aggregate/binop sites hit the
                            // existing escape guards. The RETURN site now ADMITS a THIN one (wave-14):
                            // `fn f(x:&Struct)->&Struct{x}` returns the same opaque param ptr, faithful
                            // (the return type is `Ty::Ptr`, table-free → splices). NOT added to
                            // `mut_borrow_ptrs` — there is no write path for a non-scalar pointee, so
                            // `&mut Struct` stays unregistered (its `*s = v` would need a struct
                            // memory model we do not have). The pointee value is never materialized;
                            // the ref is an opaque token that only flows into a call arg or a return.
                            // (B2 note: `&str`/`&[T]`/`&dyn` no longer reach this branch at all —
                            // map_ty signs them first-class FatPtr, so the `Ty::Ptr` gate above
                            // excludes them; their forwarding rides the fat_shared_ref reborrow
                            // lane instead. The thin_pointee exclusion below now guards only the
                            // `Foreign`/`?Sized`-residual classes.)
                            if !self.borrow_ptrs.contains(&pv) {
                                self.borrow_ptrs.push(pv);
                            }
                            // Trust (wave-14, faithfulness): only a THIN (Sized-pointee) ref may be
                            // RETURN-admitted. A fat-DST pointee (`str`/`[T]`/`dyn`/extern type)
                            // collapses to a thin `Ty::Ptr` in `map_ty` (dropping the len/vtable), so
                            // a `(ptr)->(ptr)` return sig would be ABI-UNFAITHFUL — keep those
                            // return-fail-closed (the root fix is mapping `&str`/`&dyn` to a fat tuple
                            // like `&[T]`, a separate wave that also touches the MIR oracle). Forwarding
                            // (`borrow_ptrs`) is left as-is: that thin-`&str` representation is a
                            // pre-existing wave-8a shape, out of scope here. A `?Sized` GENERIC param
                            // is an accepted thin residual (same class). This is the ONLY faithfulness
                            // gap the wave-14 adversarial review found; fail-closed is the safe answer.
                            let thin_pointee = !matches!(
                                pointee.kind(),
                                ty::Str | ty::Slice(_) | ty::Dynamic(..) | ty::Foreign(_)
                            );
                            if thin_pointee && !self.ref_param_ptrs.contains(&pv) {
                                self.ref_param_ptrs.push(pv);
                            }
                        } else if mutbl.is_mut()
                            && matches!(pointee.kind(), ty::Adt(adt, _) if adt.is_struct())
                        {
                            // Trust (wave-23, ref-escape memory model): a `&mut Struct` receiver /
                            // param. Register it (like the scalar branch's 3-way add) so BOTH
                            //   * READS  `*s` / `s.field`  (existing wave-11 Deref-Load whole
                            //     aggregate + `Field` `ExtractField` — previously fail-closed
                            //     through a `&mut` receiver because the ptr was unregistered), and
                            //   * WRITES `s.field (op)= v` (the `field_deref_place`/
                            //     `field_chain_deref_place` arms below — wave-31 extends the
                            //     plain-assign arm to nested `s.a.b = v` chains —
                            //     whole-struct `Load`→`InsertField`→`Store`)
                            // resolve. A struct pointee is inherently thin (Sized), so it is
                            // return-admissible exactly like the shared `&Struct` case (adding it to
                            // `ref_param_ptrs` keeps a returned `&mut S` param admitted, avoiding a
                            // return-escape regression). If the struct is NOT recursively
                            // registerable, `map_ty` degrades it to `Ty::Unit` and every use fails
                            // closed at the `Ty::Struct(_)` gate. Same posture as the wave-11 read:
                            // a use READS the ref param → interpreter differential `NotRun`; the
                            // shim fails closed on the opaque-`Ty::Ptr`-param `Load`/`Store` (a
                            // caller-owned slot) → NEVER a flip candidate. A `&mut` NON-struct
                            // non-scalar pointee (`&mut &T`, `&mut [T]`, `&mut dyn`, `&mut f64`)
                            // stays UNREGISTERED opaque — there is no write model for those.
                            if !self.borrow_ptrs.contains(&pv) {
                                self.borrow_ptrs.push(pv);
                            }
                            if !self.mut_borrow_ptrs.contains(&pv) {
                                self.mut_borrow_ptrs.push(pv);
                            }
                            if !self.ref_param_ptrs.contains(&pv) {
                                self.ref_param_ptrs.push(pv);
                            }
                        }
                    }
                }
            }
        }

        // Trust (wave-LDP): bind irrefutable DESTRUCTURE parameters (`fn f((a, b): (i32, i32))`,
        // `fn f(Pt { x, y }: Pt)`). Such a param has no single binding var, so `binding_var` returned
        // `None` above and `param_vars` never bound it — every use of `a`/`b` fell closed at
        // `VarRef(unbound)`. Its aggregate value is the entry block-param `ValueId::new(i)` and its
        // mapped type is `params[i]` — ALREADY mapped for the signature at `fn_sig.inputs()` above, so
        // there is NO new `map_ty` call and hence NO `became_dirty` vector (a param whose type declined
        // was tagged there and is already dirty; `emit_bind` adds no tag). Reuse the exact `let`-
        // destructure plan + `emit_bind` machinery (`ExtractField` chains + `set_local`); a `&mut`-
        // borrowed / promoted sub-local fails closed inside `emit_bind`. A destructure param is
        // non-scalar, so the interpreter differential forces `NotRun` (producer-only, never a flip).
        // Build the owned plans first (read-only over `self.thir`), then emit (the `&mut self` walk).
        let param_plans: Vec<(usize, BindNode)> = self
            .thir
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                let pat = p.pat.as_ref()?;
                if binding_var(pat).is_some() {
                    return None; // simple binding — already handled by `param_vars`
                }
                match build_bind_node(pat) {
                    Some(node @ BindNode::Fields(_)) if bind_node_binds(&node) => Some((i, node)),
                    _ => None,
                }
            })
            .collect();
        for (i, node) in param_plans {
            let ty = params.get(i).cloned().unwrap_or(Ty::Unit);
            let _ = self.emit_bind(&node, ValueId::new(i as u32), ty);
        }

        self.finish_body(module, def, func_ty_id, body);
    }

    /// Trust: lower a const/static INITIALIZER body (`BodyTy::Const`) as a ZERO-PARAM function
    /// returning the initializer value — `FuncTy { params: [], returns: [mapped ty] }` (or
    /// `returns: []` for a unit-typed const, the same unit convention fn bodies use). This is
    /// faithful by construction: `construct_const` builds exactly a zero-argument MIR body whose
    /// tail value lands in RETURN_PLACE, which is precisely the shape `finish_body`'s implicit
    /// tail-`Return` emits. The body walk shares ALL the fn expression machinery (and therefore
    /// every fail-closed gate); anything unsupported keeps its precise tag exactly as in a fn
    /// body. The caller (`lower_module`) marks the result `BodyKind::ConstInit`/`StaticInit` so
    /// initializer bodies never enter function-only lanes (the flip) unproven.
    fn lower_const_body(
        &mut self,
        module: &mut Module,
        def: LocalDefId,
        const_rty: RustcTy<'tcx>,
        body: ExprId,
    ) {
        // The `?`-operator/`return` machinery reads the declared "return" type; for an
        // initializer body that is the const's type (`typeck_results.node_type`, threaded via
        // `BodyTy::Const` — the RETURN_PLACE type NLL equates the body with).
        self.fn_return_rty = Some(const_rty);
        let returns = if const_rty.is_unit() { Vec::new() } else { vec![self.map_ty(const_rty)] };
        let func_ty_id =
            module.add_func_type(FuncTy { params: Vec::new(), returns, is_vararg: false });

        // Zero params: the entry block opens empty and value ids start at 0. A const body's
        // THIR has no params (`ThirBuildCx` seeds params only for fn-like owners) — checked,
        // not assumed.
        if !self.thir.params.is_empty() {
            self.unsupported.push(("body".to_string(), "ConstBody(unexpected params)"));
        }
        self.start_block(BlockId::new(0), Vec::new());
        self.next_value = 0;

        // Same `&mut`-promotion pre-pass as fn bodies: a const body may contain
        // `let mut y = …; let r = &mut y; *r = …` blocks, whose locals must be memory-backed.
        self.promoted = self.collect_mut_borrowed(body);

        self.finish_body(module, def, func_ty_id, body);
    }

    /// Trust: the shared body-walk tail of `lower_fn` / `lower_const_body`: walk the body
    /// expression, seal the implicit tail `Return` (with the borrow-ptr escape + unit-return
    /// gates), order the entry block first, flush pended struct/enum defs and fn-pointer
    /// `FuncTy`s (with the id-desync tripwire), and add the named `Function` to the per-body
    /// module.
    fn finish_body(
        &mut self,
        module: &mut Module,
        def: LocalDefId,
        func_ty_id: FuncTyId,
        body: ExprId,
    ) {
        let entry = BlockId::new(0);

        // Walk the body; the result (if any) lands in the currently-open fall-through block.
        let tail = self.lower_expr(body);

        // Close the final open block with an implicit tail `Return`, unless the body already sealed
        // it (explicit `return`, or an `if` where both arms diverged). Fail-closed: a borrow pointer
        // tail-returned would escape the immediate-deref-only contract — UNLESS it is a ref-PARAM
        // ptr (wave-14), which outlives the call, so returning it is faithful (the `Inst::Return`
        // below already yields `t`; we just stop tagging it). A `&local` snapshot ptr stays
        // fail-closed (not in `ref_param_ptrs`; and a returned `&local` is borrowck-rejected anyway).
        if !self.sealed {
            if let Some(t) = tail {
                // Trust (wave-16): also admit a promoted-borrow GlobalAddr pointer (`global_ptrs`) —
                // it addresses a `'static` module global, so tail-returning it is faithful (the
                // `Inst::Return` below yields the very address). A `&local` snapshot ptr stays
                // fail-closed (not in `ref_param_ptrs`/`global_ptrs`; borrowck-rejected anyway).
                // Trust (wave-25b): also admit a derived INTERIOR pointer (`interior_ptrs`) — a
                // flat-I8 GEP of a ref-param ptr to `&self.field`, addressing caller memory that
                // outlives the call, so tail-returning it is faithful (mirrors `ref_param_ptrs`).
                if self.is_borrow_ptr(t)
                    && !self.ref_param_ptrs.contains(&t)
                    && !self.global_ptrs.contains(&t)
                    && !self.interior_ptrs.contains(&t)
                {
                    self.unsupported.push(("body".to_string(), "Return(borrow ptr escapes tail)"));
                }
            }
            // Unit-returning fns return no values (the bridge convention; see `lower_fn`).
            let values = if self.fn_return_rty.is_some_and(|t| t.is_unit()) {
                Vec::new()
            } else {
                tail.into_iter().collect()
            };
            // Trust (C2-spans): the epilogue seals OUTSIDE any expr scope (the `lower_expr`
            // wrapper restored `cur_span` on exit), which left the implicit tail `Return` as
            // the one structurally unstamped terminator. Attribute it to the body's tail
            // expression — the value being returned is the location a reader wants.
            self.cur_span = self.to_source_span(self.thir.exprs[body].span);
            self.seal_with(Inst::Return { values });
        }

        // Assemble Function.blocks: entry first (so blocks[0].id == entry, matching the
        // `Function::block` index fast-path), then the remaining sealed blocks in creation order.
        let mut sealed = std::mem::take(&mut self.blocks);
        if let Some(pos) = sealed.iter().position(|b| b.id == entry) {
            let entry_block = sealed.remove(pos);
            sealed.insert(0, entry_block);
        }

        // Trust: flush any struct definitions registered during the body walk (their `StructId`s
        // were assigned positionally as they were first seen, matching `Module::add_struct`'s
        // by-`sd.id` push). Done here, after the walk, because `&mut Module` is in scope.
        for sd in std::mem::take(&mut self.pending_structs) {
            module.add_struct(sd);
        }

        // Trust: flush any GENERAL-path enum definitions registered during the body walk
        // (`register_enum`) — positional `EnumId`s, matching `Module::add_enum`'s verbatim
        // push, exactly the struct flush above.
        for ed in std::mem::take(&mut self.pending_enums) {
            module.add_enum(ed);
        }

        // Trust: flush fn-pointer signature `FuncTy`s pended during the signature mapping /
        // body walk (`pend_func_ty`). Their ids were handed out as `1 + position` — slot 0 is
        // this function's own signature, interned above before the walk — so appending in pend
        // order lines the table up with every embedded `Ty::Func` / `CallIndirect { sig }` id.
        // Tripwire (checked, not assumed): if anything else grew the table in between, the
        // handed-out ids are lies — fail the body closed rather than emit a desynced module.
        if !self.pending_func_tys.is_empty() {
            if module.func_types.len() != 1 {
                self.unsupported.push(("body".to_string(), "FnPtr(functy table desync)"));
            }
            for ft in std::mem::take(&mut self.pending_func_tys) {
                module.add_func_type(ft);
            }
        }

        // Trust: flush module-`types` entries pended during the walk (`pend_ty` — zero-length
        // array element types). Ids were handed out as positions into an EMPTY table; tripwire
        // (checked, not assumed): if anything else grew `module.types` in between, every
        // embedded `Ty::Array(TyId, _)` id is a lie — fail the body closed rather than emit a
        // desynced module.
        if !self.pending_tys.is_empty() {
            if !module.types.is_empty() {
                self.unsupported.push(("body".to_string(), "Ty(types table desync)"));
            }
            for t in std::mem::take(&mut self.pending_tys) {
                module.add_type(t);
            }
        }

        // Trust (B6): flush first-class `ClosureTy`s pended during the walk
        // (`pend_closure_ty` — by-value FnOnce closure envs). Ids were handed out as
        // positions into an EMPTY table; same desync tripwire as `pending_tys`.
        if !self.pending_closure_tys.is_empty() {
            if !module.closure_types.is_empty() {
                self.unsupported.push(("body".to_string(), "Ty(closure table desync)"));
            }
            for ct in std::mem::take(&mut self.pending_closure_tys) {
                module.add_closure_type(ct);
            }
        }

        // Trust (wave-16): flush promoted-borrow globals pended during the walk. Ids were handed
        // out as positions into an EMPTY `module.globals` table (nothing else adds to it), so
        // `pending_globals[i]` → `module.globals[i]` → `GlobalId(i)`, the id every emitted
        // `Inst::GlobalAddr { global }` embeds. Tripwire (checked, not assumed): if anything else
        // grew `module.globals` in between, those ids are lies — fail the body closed rather than
        // emit a desynced module.
        if !self.pending_globals.is_empty() {
            if !module.globals.is_empty() {
                self.unsupported.push(("body".to_string(), "Global(globals table desync)"));
            }
            for g in std::mem::take(&mut self.pending_globals) {
                module.globals.push(g);
            }
        }

        // Trust: `def_path_str`, NOT `item_name` — closure/coroutine bodies have no name
        // (`DefPathData::Closure`), so `item_name` ICEs on them; the flag-gated producer must
        // never abort a compilation that succeeds without the flag. The name is only a label on
        // this single-function module (`FuncId::new(0)`); nothing matches on it.
        // `with_no_trimmed_paths!` because a bare `def_path_str` arms `must_produce_diag`,
        // which ICEs at `DiagCtxt` drop on warning-free compiles (masked whenever RUSTC_LOG
        // is set).
        let name =
            rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(def.to_def_id()));
        let mut func = Function::new(FuncId::new(0), name, func_ty_id, entry)
            .with_producer(trust_ir::Producer::TRust);
        func.blocks = sealed;
        // Trust (C2-names, binary v32): the source-level names ledger. Empty ⇒ None, never
        // Some(empty) — absence must stay distinguishable from "named, zero names".
        if !self.value_names.is_empty() {
            func.value_names = Some(std::mem::take(&mut self.value_names));
        }
        module.add_function(func);
    }

    /// Trust: field types of a struct-shaped `ty::Adt`, mapped to interpretable `trust_ir::Ty`s, in
    /// field-declaration (index) order. Returns `None` (fail-closed) for a non-struct Adt
    /// (enum/union), or when any field type is unsupported (its own `unsupported` entry is recorded
    /// by the recursive `map_ty`, and the seed-interpretability check in the caller fails closed).
    fn struct_field_tys(
        &mut self,
        adt: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Option<Vec<Ty>> {
        // Multi-variant (enum) and union Adts are not lowered: their variant/overlap layout model is
        // a separate step. A struct has exactly one (the non-enum) variant.
        if !adt.is_struct() {
            return None;
        }
        // Cycle guard: a recursive INSTANTIATION re-entering its own field mapping fails
        // closed (see `adt_visit_stack`) — the type's fixpoint is not representable in the
        // producer's structural Ty model, and unguarded recursion is a stack-overflow
        // SIGBUS, not an error. Keyed (DefId, args): nested distinct instantiations of the
        // same generic struct (typenum towers) are a DAG walk, not a cycle (Batch B).
        if self.adt_visit_stack.contains(&(adt.did(), args)) {
            self.unsupported.push((format!("{:?}", adt.did()), "Ty(recursive adt)"));
            return None;
        }
        // Depth fuel: (DefId, args) keying alone does not terminate on polymorphic
        // recursion behind pointers (unboundedly many distinct pairs) — bound the depth.
        if self.adt_visit_stack.len() >= ADT_VISIT_FUEL {
            self.unsupported.push((format!("{:?}", adt.did()), "Ty(adt-depth)"));
            return None;
        }
        self.adt_visit_stack.push((adt.did(), args));
        let tcx = self.tcx;
        let field_rtys: Vec<RustcTy<'tcx>> = adt
            .non_enum_variant()
            .fields
            .iter()
            .map(|f| f.ty(tcx, args).skip_normalization())
            .collect();
        let mapped = field_rtys
            .into_iter()
            .map(|t| {
                let m = self.map_ty(t);
                // Trust (wave-RS): under `TRUST_OPTION_FLAG_LANES=1`, an opaque `Option`
                // lane must register `Ty::Bool` (the DISCRIMINANT tag) through EVERY
                // builder — `struct_ty_rmw_opaque` already does; without this mirror a
                // plain-`map_ty` profile of the SAME struct kept `Ty::Unit` at the lane
                // (measured flag-ON: GridStorage clone id=85 disagreed with the rmw
                // profiles at lane 8), so table-level clone-agreement checks (and any
                // reader keyed on the lane type) saw a split identity. A `Ty::Unit`
                // mapping of the Option lang enum is EXACTLY the opaque-Option shape (a
                // pure `Option<scalar>` maps to a real enum/tuple repr, never `Unit`).
                if option_flag_lanes_enabled()
                    && m == Ty::Unit
                    && matches!(t.kind(), ty::Adt(a, _)
                        if tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
                {
                    Ty::Bool
                } else {
                    m
                }
            })
            .collect();
        self.adt_visit_stack.pop();
        Some(mapped)
    }

    /// Trust (opaque-field RMW, this wave): build the whole-struct `Ty::Struct` for a
    /// `(*p).field = v` / `(*p).field op= v` read-modify-write in which SIBLING fields the
    /// annotated method never touches may be NON-pure-value (a `Vec`, an `Option<T>`, a
    /// data-carrying enum — the real `GridStorage` shape). Each field is mapped as usual; a
    /// sibling that either fails to map cleanly OR is not a pure value is replaced by an OPAQUE
    /// placeholder (`Ty::Unit`) — the value round-trips through `Load`/`InsertField`/`Store` with
    /// that lane untouched, and any `unsupported` entry the failed map recorded is ROLLED BACK
    /// (the sibling is deliberately not lowered, not a coverage gap). The WRITTEN field must still
    /// map to a genuine scalar (else `None`: we cannot express the store).
    ///
    /// Soundness boundary: these bodies are structurally `NotRun` (the `Load` reads the opaque
    /// `&mut`-param pointee; the interpreter shim fails closed on the opaque-param `Load`/`Store`),
    /// so the placeholder is never dynamically executed or byte-differentially compared. The only
    /// consumer is the temporal extractor, which reads fields BY DECLARATION-ORDER INDEX (preserved
    /// here — exactly one placeholder per opaque sibling, so every projected index still binds to
    /// its field) and never touches the opaque lanes. This deliberately relaxes the old blanket
    /// `is_pure_value_shape` gate (whose fat/thin-collapse faithfulness concern is a run-time
    /// property, moot for a `NotRun` body) to the SCALAR- WRITTEN-FIELD it actually needs.
    ///
    /// Determinism across a body's multiple writes: a scalar sibling stays a real scalar and a
    /// non-pure sibling stays opaque regardless of which field is the current `written_field`, so
    /// every write in a body registers IDENTICAL field types (a non-scalar written field returns
    /// `None` BEFORE `register_struct`, so no divergent registration is ever committed). Cycle
    /// guard mirrors `struct_field_tys` (a self/mutually-recursive pointee declines, never opaques).
    ///
    /// `written_field` is `Some(i)` at a WRITE site (`(*p).field = v` — lane `i` must be a real
    /// scalar) and `None` at a whole-struct READ site (`*self` loaded then `ExtractField`ed — no
    /// single required lane; each read field is scalar-gated by the `Field`/`ExtractField` arm). A
    /// pure-value struct maps IDENTICALLY through either mode and identically to plain `map_ty`, so
    /// routing BOTH the write RMW and the whole-struct read through this one builder keeps the
    /// per-body `register_struct` (dedup by `(DefId, GenericArgs)`, B3-4) registration deterministic — the read and the
    /// write of the same `GridStorage` agree on which lanes are opaque, regardless of walk order.
    fn struct_ty_rmw_opaque(
        &mut self,
        adt: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        written_field: Option<u32>,
    ) -> Option<Ty> {
        if !adt.is_struct() {
            return None;
        }
        if self.adt_visit_stack.contains(&(adt.did(), args)) {
            return None;
        }
        self.adt_visit_stack.push((adt.did(), args));
        let tcx = self.tcx;
        let field_rtys: Vec<RustcTy<'tcx>> = adt
            .non_enum_variant()
            .fields
            .iter()
            .map(|f| f.ty(tcx, args).skip_normalization())
            .collect();
        let mut field_tys: Vec<Ty> = Vec::with_capacity(field_rtys.len());
        // A read site (`written_field == None`) requires no specific scalar lane.
        let mut written_ok = written_field.is_none();
        for (i, rty) in field_rtys.into_iter().enumerate() {
            let before = self.unsupported.len();
            let mapped = self.map_ty(rty);
            let clean = self.unsupported.len() == before;
            if Some(i as u32) == written_field {
                // The one lane we actually write must be a real, faithfully-mapped scalar.
                written_ok = clean && is_scalar_ty(&mapped);
                field_tys.push(mapped);
                continue;
            }
            // A sibling: keep its real type if it maps cleanly AND is a pure value (so the
            // whole-struct round-trip stays faithful for it). Otherwise roll back any gap the
            // failed map recorded and decide the opaque lane:
            //
            // Trust (wave-EL): an OPAQUE-LANE DATA ENUM sibling now maps CLEAN (`Ty::Unit`, no
            // tag), and its `fat_shape` can be PURE (e.g. `Option<RepaintKey>` over an
            // all-scalar payload struct), which would divert it into the pure branch — pushing
            // the same `Ty::Unit` but SKIPPING the else-branch's lane decisions (the
            // wave-OPTFLAG `Ty::Bool` discriminant registration in particular; measured: the
            // present-real fixture regressed `bool, bool` → `(), ()` without this). Pre-wave,
            // every such sibling was UNCLEAN and always took the else branch — pin that exact
            // branch selection with the explicit enum predicate.
            //   * a LOCAL struct sibling/holder (the two-level `self.storage.<scalar>` shape) is
            //     RECURSED through this SAME deterministic builder (`written_field = None`), so its
            //     inner SCALARS stay reachable as a registered `Ty::Struct` lane while ITS own
            //     non-pure siblings go opaque — read and write both hit this build, so the nested
            //     registration agrees (`register_struct` dedups by `(DefId, GenericArgs)`, B3-4);
            //   * everything else (std containers `Vec`/`Option`, data-enums, refs/ptrs, or a
            //     recursion that declines, e.g. a self-recursive holder) collapses to `Ty::Unit`.
            let pure = clean
                && !self.is_opaque_lane_enum(rty)
                && is_pure_value_shape(&self.fat_shape(rty, &mut Vec::new()));
            if pure {
                field_tys.push(mapped);
            } else {
                self.unsupported.truncate(before);
                // Trust (wave-OPTFLAG): under `TRUST_OPTION_FLAG_LANES=1`, a provably-opaque
                // `Option<T>` sibling — EXACTLY the shape that collapses to `Ty::Unit` below
                // (the Option lang enum whose payload is non-pure-value; a pure
                // `Option<scalar>` never reaches this else-branch) — registers as a `Ty::Bool`
                // DISCRIMINANT lane instead, so a literal variant store can carry `Some`/`None`
                // distinguishably (see `option_flag_lanes_enabled`). Flag off: byte-identical.
                if option_flag_lanes_enabled()
                    && matches!(rty.kind(), ty::Adt(a, _)
                        if tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
                {
                    field_tys.push(Ty::Bool);
                    continue;
                }
                let recursed = match rty.kind() {
                    ty::Adt(a, ga) if a.is_struct() && a.did().is_local() => {
                        self.struct_ty_rmw_opaque(*a, *ga, None)
                    }
                    _ => None,
                };
                field_tys.push(recursed.unwrap_or(Ty::Unit));
            }
        }
        self.adt_visit_stack.pop();
        if !written_ok {
            return None;
        }
        Some(Ty::Struct(self.register_struct(adt, args, &field_tys)))
    }

    /// Trust: register a struct `AdtDef` ONCE (dedup by its `DefId`), returning the assigned
    /// `StructId`. The `StructDef` carries the struct's name and (interpretable) field types; the
    /// runtime struct *value* is FIRST-CLASS `Ty::Struct(id)` (the pinned interpreter materializes
    /// `(Ty::Struct, Constant::Aggregate)` seeds — foundations 93e8f16, scratch-verified). Field
    /// mapping is depth-first (`struct_field_tys` recurses via `map_ty` BEFORE this push), so a
    /// nested struct field's id is always LESS than its parent's — the splice's remap-order
    /// invariant (crate_module.rs checks it, never assumes).
    fn register_struct(
        &mut self,
        adt: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        field_tys: &[Ty],
    ) -> trust_ir::StructId {
        let did = adt.did();
        // Batch B: dedup by INSTANTIATION — see the `struct_ids` field doc.
        if let Some((_, _, id)) = self.struct_ids.iter().find(|(d, a, _)| *d == did && *a == args) {
            return *id;
        }
        // Positional id: matches `Module::add_struct` pushing by `sd.id` and the count of
        // already-registered structs (we are the only registrant in this single-function module).
        let id = trust_ir::StructId::new(self.struct_ids.len() as u32);
        // Instantiation-qualified identity keeps distinct generic layouts
        // deterministic across bodies and registration order.
        let name = rustc_middle::ty::print::with_no_trimmed_paths!(
            self.tcx.def_path_str_with_args(did, args)
        );
        // Trust (B3-4 T2): fill the declared layout FAITHFULLY when a concrete
        // layout exists; leave every layout field `None` otherwise (absent-fill
        // == pre-T2 behavior — registration itself NEVER fails on layout, so
        // generic bodies keep their clean rate). Single mint site => the fill is
        // deterministic per (DefId, args) across all registration funnels.
        // Offsets are READ ONLY from rustc's authoritative
        // `layout.fields.offset` in SOURCE-DECLARATION index (FieldsShape is
        // reorder-aware; never hand-compute — the wave-25b rule). The
        // re-entrancy pre-gate mirrors `lower_offset_of`: `layout_of` on a
        // param/infer/opaque/bound-bearing type can ICE in a query, not `Err`.
        let struct_rty = ty::Ty::new_adt(self.tcx, adt, args);
        let layout = if layout_query_is_reentrant_safe(struct_rty) {
            let te = ty::TypingEnv::fully_monomorphized();
            self.tcx.layout_of(te.as_query_input(struct_rty)).ok()
        } else {
            None
        };
        let (size, align) = match &layout {
            Some(l) => (Some(l.size.bytes()), Some(l.align.abi.bytes())),
            None => (None, None),
        };
        // Repr hint: `#[repr(transparent)]` > packed clamp > `#[repr(C)]` >
        // default Rust. `repr(C, packed(N))` collapses to `Packed` — the
        // StructRepr carrier holds ONE hint; the filled size/align/offsets
        // carry the actual bytes either way.
        let repr = {
            let r = adt.repr();
            if r.transparent() {
                trust_ir::StructRepr::Transparent
            } else if let Some(pack) = r.pack {
                trust_ir::StructRepr::Packed(pack.bytes() as u32)
            } else if r.c() {
                trust_ir::StructRepr::C
            } else {
                trust_ir::StructRepr::Rust
            }
        };
        let fields = adt
            .non_enum_variant()
            .fields
            .iter()
            .zip(field_tys)
            .enumerate()
            .map(|(i, (f, ty))| trust_ir::FieldDef {
                name: f.name.to_string(),
                ty: ty.clone(),
                // Trust: `FieldsShape::offset` PANICS out of range (rustc_abi
                // `offsets[FieldIdx::new(i)]`) — and a struct's layout can
                // carry FEWER field entries than the AdtDef variant has
                // (e.g. `#[rustc_scalable_vector]` structs lay out as a
                // vector shape). Bounds-check and drop the offset instead of
                // aborting the compile (producer totality: fail closed to a
                // missing offset, never to an ICE).
                offset: layout
                    .as_ref()
                    .filter(|l| i < l.fields.count())
                    .map(|l| l.fields.offset(i).bytes()),
            })
            .collect();
        self.pending_structs.push(trust_ir::StructDef { id, name, fields, size, align, repr });
        self.struct_ids.push((did, args, id));
        id
    }

    /// Trust: the field types of an already-registered struct, by its `StructId` (declaration
    /// order — the same order `ExprKind::Adt` writes and `Field` reads). `None` (fail-closed)
    /// for an unregistered id — impossible for a `Ty::Struct` freshly produced by `map_ty`,
    /// but checked, never assumed.
    fn registered_struct_field_tys(&self, sid: trust_ir::StructId) -> Option<Vec<Ty>> {
        self.pending_structs
            .iter()
            .find(|sd| sd.id == sid)
            .map(|sd| sd.fields.iter().map(|f| f.ty.clone()).collect())
    }

    /// Trust (wave-12): a well-typed placeholder `Constant` for `ty`, used ONLY as the aggregate
    /// SEED that a following `InsertField` chain fully overwrites (every field is written before
    /// the value is read, so the seed's values are never observed — it exists solely to give the
    /// `Inst::Const` a structurally-well-typed aggregate the interpreter can materialize). This is
    /// the recursive counterpart of the free `seed_constant`: scalar leaves delegate to it
    /// unchanged, but a NESTED aggregate field gets a structurally-matching `Constant::Aggregate`
    /// so struct/tuple-of-struct construction no longer fails closed at the seed. The interpreter's
    /// `constant_to_value` materializes `(Ty::Struct, Aggregate)` / `(Ty::Tuple, Aggregate)`
    /// per-field (interpret.rs), so a nested-aggregate seed round-trips through Store/Load/
    /// ExtractField exactly as an `InsertField`-built value would. `Ty::Struct(sid)` reads the
    /// registered field types (`registered_struct_field_tys` — the SAME declaration order the
    /// seed/`InsertField` indices use); `Ty::Tuple` carries its element types inline.
    ///
    /// Fail-closed (`None`) for any non-seedable leaf (Ptr/Array/Enum/Unit/f16/…): the recursion
    /// bottoms out on EXACTLY the scalar set the flat `seed_constant` accepts, so a field the
    /// interpreter could not materialize declines the WHOLE construction (never a mis-typed
    /// placeholder). Termination: the recursion descends ONLY through by-value `Ty::Struct`/
    /// `Ty::Tuple`, whose nesting is finite — a by-value self/mutually-recursive struct is
    /// impossible in Rust (infinite size), so a recursive type routes through a reference
    /// (`&`/`&mut` → `Ty::Ptr` directly) or `Box` (a lang-item struct whose deep field bottoms out
    /// at a raw pointer → `Ty::Ptr`), a non-seedable leaf either way. Decisively, `register_struct`
    /// interns inner-before-outer, so the registered-struct DAG's Struct edges strictly decrease in
    /// id — termination in ≤ (#registered structs) steps. The `depth` cap is a redundant backstop,
    /// not the termination argument.
    fn seed_constant_ty(&self, ty: &Ty, depth: usize) -> Option<Constant> {
        if depth > 64 {
            return None;
        }
        match ty {
            Ty::Tuple(elems) => elems
                .iter()
                .map(|e| self.seed_constant_ty(e, depth + 1))
                .collect::<Option<Vec<_>>>()
                .map(Constant::Aggregate),
            Ty::Struct(sid) => {
                let fields = self.registered_struct_field_tys(*sid)?;
                fields
                    .iter()
                    .map(|f| self.seed_constant_ty(f, depth + 1))
                    .collect::<Option<Vec<_>>>()
                    .map(Constant::Aggregate)
            }
            // Trust (wave-ES): a general first-class `Ty::Enum(eid)` FIELD seeds as variant-0's
            // aggregate placeholder `[Int(disc0), field_seeds...]` — the SAME shape `map_ty`
            // documents (867) and `lower_enum_construct` emits (7678). `register_enum` walls every
            // variant field to a seedable scalar OR a nested first-class enum (Trust B3-3 —
            // this arm recurses into a nested field; inner-before-outer ids + the depth cap
            // terminate), so variant 0's fields all seed; this `Const`
            // placeholder is overwritten WHOLESALE by the `InsertField` that stores the real enum
            // value at the aggregate's field index (every `seed_constant_ty` caller overwrites each
            // lane), so its internal shape never escapes. Fail-closed (`None` → the caller records
            // its non-scalar-seed tag) on an unregistered eid, an uninhabited enum (no variant 0), a
            // missing discriminant, or a non-scalar variant-0 field — none reachable for a
            // map_ty-produced `Ty::Enum`, all checked. This clears the `Ty::Enum`-field subset of
            // `Adt`/`Tuple`/`Array(non-scalar field/element seed)` (struct/tuple/array holding an
            // enum field) that previously fell closed; a body that was already clean never reached
            // this arm, so became_dirty == 0.
            Ty::Enum(eid) => {
                let ed = self.registered_enum(*eid)?;
                let v0 = ed.variants.first()?;
                let disc0 = ed.discriminants.first().copied().flatten()?;
                let mut seed = Vec::with_capacity(1 + v0.fields.len());
                seed.push(Constant::Int(disc0));
                for fty in &v0.fields {
                    seed.push(self.seed_constant_ty(fty, depth + 1)?);
                }
                Some(Constant::Aggregate(seed))
            }
            // Trust (wave-FRU batch, L3): a zero-length array field `[T; 0]` (map_ty sends `[T; N>0]`
            // to `Ty::Tuple`, so a `Ty::Array` seed is only ever `N == 0`) is a ZST — seed as the empty
            // array constant, byte-identical to what `ExprKind::Array` emits for `[]`. Completes the
            // wave-13 array-seed family; became_dirty == 0 (a `[T; 0]` field fell to the scalar `_`
            // arm → `None` → the caller's `…non-scalar field seed` tag before this wave).
            Ty::Array(_, 0) => Some(Constant::Array(Vec::new())),
            // Trust (wave-UF): a `()` unit FIELD/element (a struct's `u: ()`, a tuple's `(a, ())`,
            // a nested unit) is a ZERO-SIZE type with a single inhabitant — seed it as the
            // interpreter's zero-size placeholder `Constant::PhantomData` (interpret.rs:1706 accepts
            // `(_, PhantomData)` against ANY type incl `Ty::Unit`). For a unit aggregate FIELD the
            // caller emits NO `InsertField` (its value is value-less — the producer models `()` as
            // producing no value, see [[unit-typed-local-read-is-valueless-noop]]), so this seed is
            // the field's FINAL value; being the sole inhabitant it cannot differ from built-MIR's
            // own `()`, so the aggregate is flip-faithful by construction. For a nested-struct field
            // (`Outer { inner: Inner { u: () } }`) the whole `Inner` slot is overwritten by an
            // `InsertField`, so the placeholder never escapes there. Fail-closed elsewhere
            // unchanged. (wave-EL: the opaque-lane `Ty::Unit` — a data-enum/Option/Vec sibling the
            // opaque builders collapsed — reaches this SAME PhantomData seed, which is what lets a
            // struct LITERAL with an opaque enum lane, e.g. `ReflowedScrollback { store, .. }`,
            // construct: the seed lane is overwritten by the `InsertField` of the field's own
            // opaque unit value.)
            Ty::Unit => Some(Constant::PhantomData),
            _ => seed_constant(ty),
        }
    }

    /// Trust: register an enum `AdtDef` instantiation ONCE for the GENERAL first-class
    /// `Ty::Enum` path (dedup by `(DefId, GenericArgs)` — see the `enum_ids` field doc for why
    /// `DefId` alone would alias generic instantiations), returning the assigned `EnumId`, or
    /// `None` (the enum then TYPES as the wave-EL opaque `Ty::Unit` lane; every OPERATION on it
    /// outside the admitted opaque-flow channels keeps its own fail-closed tag).
    ///
    /// The `EnumDef` carries variant names + field types, EXPLICIT per-variant discriminants
    /// (rustc's `discriminant_for_variant`, sign-extended by the discriminant type's own
    /// signedness — the value a `Switch` case and the constant seed's leading `Int` both carry,
    /// single source of truth), and the `#[repr(iN)]` tag hint. ADMISSION GATE (all checked,
    /// never assumed):
    ///   * every variant field of EVERY variant must be a seedable scalar
    ///     (`seed_constant`: ints/bool/floats). This is what makes the pinned interpreter's
    ///     `enum_layout` PROVABLY computable — the layout sizes ALL variants at the first
    ///     construction/store of the enum, so one unsizable field in a never-constructed
    ///     variant would trap every construction (a manufactured differential divergence).
    ///     It also keeps registered defs table-free, the splice's enums-first intern
    ///     precondition (`crate_module::splice_ok` re-checks).
    ///   * `canonical_tag_repr()` must resolve on the BUILT def (uninhabited enums,
    ///     discriminants beyond the 64-bit tag cap, or a too-narrow repr hint all decline) —
    ///     the same call the interpreter makes, so tag-lane agreement is by construction.
    ///   * recursion declines via `adt_visit_stack` (mirrors `struct_field_tys`).
    fn register_enum(
        &mut self,
        adt: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Option<trust_ir::EnumId> {
        if !adt.is_enum() {
            return None;
        }
        let did = adt.did();
        if let Some((_, _, id)) = self.enum_ids.iter().find(|(d, a, _)| *d == did && *a == args) {
            return Some(*id);
        }
        // Negative cache: a DECLINED enum must short-circuit too. Without it, a
        // macro-generated tower (enum_N wrapping enum_{N-1} in each of V variants, every
        // level declining on its non-scalar fields) re-walks each level once per variant
        // above it — V^depth failed registrations. tests/ui/enum/issue-42747.rs (a
        // ~50-level, 4-variant tower) hung the compiler until this cache existed.
        if self.enum_declined.iter().any(|(d, a)| *d == did && *a == args) {
            return None;
        }
        if self.adt_visit_stack.contains(&(did, args)) {
            self.unsupported.push((format!("{did:?}"), "Ty(recursive adt)"));
            return None;
        }
        // Trust (B3-2b): the field walk is a PROBE. Post-2b register_enum runs FIRST
        // on EVERY enum (the dispatch key), so its map_ty calls now reach field types
        // the legacy/opaque lanes handle silently (Option<fn()>, contract-closure
        // storage, Option<Void>). map_ty tags unsupported types as a side effect —
        // leaking those tags on an enum we then DECLINE marks bodies dirty whose
        // actual lowering is byte-identical (7 corpus regressions, all tag-only).
        // Snapshot + truncate on decline; a REGISTERED enum's fields all mapped, so
        // nothing real is ever dropped.
        let probe_tags = self.unsupported.len();
        // Depth fuel — see `adt_visit_stack`/`ADT_VISIT_FUEL` (Batch B).
        if self.adt_visit_stack.len() >= ADT_VISIT_FUEL {
            self.unsupported.push((format!("{did:?}"), "Ty(adt-depth)"));
            return None;
        }
        self.adt_visit_stack.push((did, args));
        let tcx = self.tcx;
        let mut variants: Vec<trust_ir::EnumVariant> = Vec::with_capacity(adt.variants().len());
        let mut fields_ok = true;
        'variants: for variant in adt.variants() {
            let mut fields = Vec::with_capacity(variant.fields.len());
            // `None` is the struct-like form; tuple/unit constructors are
            // positional and therefore intentionally carry no field names.
            let named_fields = variant.ctor_kind().is_none();
            let mut field_names =
                if named_fields { Vec::with_capacity(variant.fields.len()) } else { Vec::new() };
            for f in &variant.fields {
                let rust_fty = f.ty(tcx, args).skip_normalization();
                // Trust (B3-2c E1): a DROP-FREE ZST field admits as the CANONICAL
                // `Ty::Unit` — the forced respell minted at admission, tested on the
                // GROUND-TRUTH rustc type (never the mapped ty: map_ty also emits
                // Unit for wave-EL opaque collapses, and keying on it would silently
                // zero-size a LIVE payload). This is what migrates the wave-EZ
                // family (fmt::Result, Option<()>, Poll<()>) first-class: fmt::Error
                // must NEVER enter the def as Ty::Struct(sid) — a table-bearing
                // field fails splice_ok's ty_table_free and refuses the whole-body
                // splice (the enum-struct-payload NO-GO lesson). Drop-bearing ZSTs
                // keep declining through the scalar wall below. INVARIANT: inside a
                // registered EnumDef, field ty == Ty::Unit iff the rustc field is a
                // drop-free ZST; ctor/match sites key on the DEF field ty only.
                if self.is_drop_free_zst(rust_fty) {
                    fields.push(Ty::Unit);
                    if named_fields {
                        field_names.push(f.name.to_string());
                    }
                    continue;
                }
                let fty = self.map_ty(rust_fty);
                // Seedable wall: scalar fields (ints/bool/floats) pass via
                // seed_constant; a NESTED first-class enum field passes too
                // (Trust B3-3 — `map_ty` registers the nested def FIRST, so a
                // `Ty::Enum` here is registered by construction with an id
                // strictly smaller than the outer's, and `seed_constant_ty`'s
                // wave-ES arm seeds it recursively as its variant-0 value).
                // Anything else — non-enum aggregates, refs/ptrs — still
                // declines the WHOLE enum (see the gate doc).
                if seed_constant(&fty).is_none() && !matches!(fty, Ty::Enum(_)) {
                    fields_ok = false;
                    break 'variants;
                }
                fields.push(fty);
                if named_fields {
                    field_names.push(f.name.to_string());
                }
            }
            variants.push(trust_ir::EnumVariant {
                name: variant.name.to_string(),
                fields,
                field_names,
            });
        }
        self.adt_visit_stack.pop();
        if !fields_ok {
            self.unsupported.truncate(probe_tags);
            self.enum_declined.push((did, args));
            return None;
        }
        let (discriminants, repr) = match (self.enum_discriminants(adt), enum_repr_hint(adt)) {
            (Some(d), Some(r)) => (d, r),
            _ => {
                self.enum_declined.push((did, args));
                return None;
            }
        };
        let id = trust_ir::EnumId::new(self.enum_ids.len() as u32);
        let name = self.tcx.item_name(did).to_string();
        let mut def = trust_ir::EnumDef::new(id, name, variants)
            .with_discriminants(discriminants.into_iter().map(Some).collect());
        if let Some(r) = repr {
            def = def.with_repr(r);
        }
        // The interpreter's layout gate, run HERE at registration (checked, not assumed): a
        // def with no canonical tag (duplicate/overflowing discriminants, hint too narrow,
        // zero variants) would trap at its first construction — decline instead.
        if def.canonical_tag_repr().is_none() {
            self.enum_declined.push((did, args));
            return None;
        }
        // Trust (B3-3): fill the CONCRETE layout descriptor from rustc's own
        // layout query (the B3-4 T2 struct-fill mirror; absent-fill posture —
        // registration never fails on layout). NORMATIVE when present, so the
        // fill declines to None on anything the v31 grammar cannot express
        // faithfully. Decline rules are the LOCKSTEP MIRROR of the oracle
        // chain (trust-mir-extract `extractor_enum_layout_info` + the
        // trust-ir-bridge canonical-width copy-through gate); a drifted rule
        // surfaces as a descriptor presence/content asymmetry in `tys_agree`
        // (coverage-only Err — the drift tripwire), never a divergence.
        let rust_ty = ty::Ty::new_adt(self.tcx, adt, args);
        def.layout = cycle_safe_layout_of(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            rust_ty,
        )
        .and_then(|l| producer_enum_layout_descriptor(&def, adt, &l));
        self.pending_enums.push(def);
        self.enum_ids.push((did, args, id));
        Some(id)
    }

    fn registered_enum(&self, eid: trust_ir::EnumId) -> Option<&trust_ir::EnumDef> {
        self.pending_enums.iter().find(|ed| ed.id == eid)
    }

    /// Trust: every variant's discriminant VALUE for `adt`, in variant order — rustc's
    /// `discriminant_for_variant(...).val` bit pattern reinterpreted through the discriminant
    /// type's own width/signedness (`sign_extend`), so `Ordering::Less = -1` yields `-1i128`,
    /// not the raw two's-complement pattern. This is the ONE place general-path discriminants
    /// are computed; the `EnumDef`, the construction seed, and every `Switch` case all read the
    /// registered def, so they agree by construction. FAIL-CLOSED `None`: a non-integer or
    /// 128-bit-wide discriminant type (a `u128` pattern above `i128::MAX` would WRAP under
    /// reinterpretation — never guess).
    fn enum_discriminants(&mut self, adt: ty::AdtDef<'tcx>) -> Option<Vec<i128>> {
        let tcx = self.tcx;
        let mut out = Vec::with_capacity(adt.variants().len());
        for (vidx, _) in adt.variants().iter_enumerated() {
            let discr = adt.discriminant_for_variant(tcx, vidx);
            let (bits, signed): (u32, bool) = match discr.ty.kind() {
                // isize/usize discriminant types take the producer's uniform 64-bit collapse
                // (`bit_width()` is `None` for pointer-sized ints).
                ty::Int(ity) => (ity.bit_width().unwrap_or(64) as u32, true),
                ty::Uint(uty) => (uty.bit_width().unwrap_or(64) as u32, false),
                _ => return None,
            };
            if bits > 64 {
                // 128-bit discriminants exceed the canonical tag cap; reinterpreting a u128
                // pattern > i128::MAX would wrap negative — decline, never mis-tag.
                return None;
            }
            out.push(sign_extend(discr.val, signed, bits));
        }
        Some(out)
    }

    /// Trust (wave-EZ): `true` iff `ty` is a Drop-free zero-sized type — layout-inert, so as an
    /// enum variant payload it is fieldless-EQUIVALENT (contributes 0 bytes). The explicit
    /// re-entrancy guard rejects generic/inferred/opaque/bound-bearing inputs before `layout_of`:
    /// inside `mir_built`, such a query can cycle through opaque `type_of`/borrowck instead of
    /// returning an error. Only for a CONCRETE ZST is `needs_drop` consulted (a ZST with a `Drop`
    /// impl has an observable drop effect → `false`).
    fn is_drop_free_zst(&self, ty: ty::Ty<'tcx>) -> bool {
        if !layout_query_is_reentrant_safe(ty) {
            return false;
        }
        let te = ty::TypingEnv::fully_monomorphized();
        match cycle_safe_layout_of(self.tcx, te, ty) {
            Some(layout) if layout.is_zst() => !cycle_safe_needs_drop(self.tcx, te, ty),
            _ => false,
        }
    }

    /// Lower one THIR statement into the current block / binding environment.
    fn lower_stmt(&mut self, id: StmtId) {
        enum Action {
            Expr(ExprId),
            Let(Option<LocalVarId>, Option<ExprId>),
            // Trust (wave-LD): an irrefutable `let`-destructure (`let (a, b) = init;`) — the owned
            // binding plan + the init expr. `BindNode` carries no lifetime, and the init's type is
            // re-read from `self.thir` in the emit arm, so this local enum needs no `'tcx` (a local
            // item cannot name the impl's lifetime).
            LetDestructure(BindNode, ExprId),
            // Trust (wave-ER): `let PAT = init else { … };` — (pattern binding vars if the
            // pattern is an admissible variant test, the initializer, the else block, the
            // pattern span for tags).
            // Trust (wave-SEAM): also carries the tested Option variant (`Some`-test flag)
            // for the value-lane arm of `lower_let_opaque_test`.
            LetElse(
                Option<Vec<LocalVarId>>,
                Option<bool>,
                Option<ExprId>,
                rustc_middle::thir::BlockId,
                String,
            ),
            // Trust (wave-TD, 2026-07-14): `let (a, _b, …) = init;` — a plain TUPLE
            // destructure (one `Option<LocalVarId>` slot per tuple position; `None` =
            // wildcard/elided) over a lowerable initializer. See the handler below for
            // the admission conditions and the wave-SEAM ledger extension.
            LetTuple(Vec<Option<LocalVarId>>, Option<ExprId>),
        }
        let action = {
            let stmt = &self.thir.stmts[id];
            match &stmt.kind {
                StmtKind::Expr { expr, .. } => Action::Expr(*expr),
                StmtKind::Let { pattern, initializer, else_block, .. } => {
                    if let Some(else_blk) = else_block {
                        // Trust (wave-ER): a let-`else` statement. The PRE-wave arm below
                        // silently DROPPED the else block (an early-return arm, possibly with
                        // effects) whenever the pattern was not a plain binding — a body could
                        // lower "clean" while modeling neither the else effects nor the branch
                        // (silent unsoundness, probe-confirmed). Route to the dedicated
                        // lowering: either the opaque-enum let-test machinery lowers it as a
                        // real CFG branch, or the statement fails closed with a precise tag.
                        Action::LetElse(
                            self.let_pat_bindings(pattern),
                            Self::option_pat_variant_test(pattern),
                            *initializer,
                            *else_blk,
                            format!("{:?}", pattern.span),
                        )
                    } else {
                        // A simple binding (`let x = …`) → the existing `Let` path (closures,
                        // promoted slots, shadowing all handled there). A non-binding pattern is
                        // routed IN ORDER (merge of the parallel session's wave-LD `LetDestructure`
                        // and the wave stack's wave-TD `LetTuple`): FIRST the plain TUPLE
                        // destructure (wave-TD — `let (_seq, evicted) = …;`, which also carries the
                        // wave-SEAM `option_lane_values` ledger for its opaque-lane-Option
                        // components); THEN the GENERAL irrefutable destructure (wave-LD — struct
                        // `let P { x, y } = …`, array `let [a, b] = …`, nested combinations) when it
                        // BINDS at least one local. Both emit the same `ExtractField` binds for a
                        // tuple, so tuples routed to `LetTuple` stay dump-identical to `LetDestructure`
                        // (the ledger push is flag-gated, IR-inert). Every other `None` shape
                        // (wildcard `let _`, an unmodeled pattern, or no initializer) keeps the
                        // pre-wave behaviour: lower the init for effects, bind nothing.
                        match binding_var(pattern) {
                            Some(var) => Action::Let(Some(var), *initializer),
                            None => match tuple_pat_bindings(pattern) {
                                Some(binds) => Action::LetTuple(binds, *initializer),
                                None => match (build_bind_node(pattern), *initializer) {
                                    (Some(node @ BindNode::Fields(_)), Some(init))
                                        if bind_node_binds(&node) =>
                                    {
                                        Action::LetDestructure(node, init)
                                    }
                                    _ => Action::Let(None, *initializer),
                                },
                            },
                        }
                    }
                }
            }
        };
        match action {
            Action::Expr(e) => {
                // Trust (wave-22): a bare-statement closure/coroutine LITERAL (`|…| {…};`,
                // `async {…};`, `#[coroutine] || {…};`) is CONSTRUCTED and immediately DISCARDED —
                // the expression-statement value is dropped, and a closure literal is never CALLED
                // nor a future POLLED at construction, so its body executes NOTHING here.
                // Construction only captures upvars (trap-free place copies/borrows); the sole
                // residual effect is the drop of any moved-in captures, which the producer models
                // NOWHERE (uniformly Drop-agnostic). So the statement is a no-op WITHIN the
                // producer's existing scope — skip it, exactly as the `let`-bound non-capturing
                // closure case below. A CALLED closure `(|| …)()` peels to `ExprKind::Call`, not
                // `Closure`, so it is unaffected and lowers normally via `ClosureCall`.
                if self.closure_literal(e) {
                    return;
                }
                let _ = self.lower_expr(e);
            }
            Action::Let(var, Some(init)) => {
                // Trust: wave-5 — `let f = |…| …;` binding a NON-CAPTURING plain-closure
                // LITERAL. Constructing a capture-free closure evaluates NOTHING (an empty
                // `upvars` list means no operand subexpressions exist) and produces a
                // zero-sized value, so there is no instruction to emit and the local is
                // deliberately left UNBOUND. This is fail-closed, not a hole:
                //   * the one modeled consumer — the `ClosureCall` receiver position
                //     (`effect_free_closure_receiver`) — never reads the local's VALUE (the
                //     callee identity comes from the `FnDef` type, and behaviour cannot depend
                //     on which runtime instance of a capture-free closure is named);
                //   * every OTHER use keeps failing closed at its own site via the existing
                //     unbound-local tags ("VarRef(unbound)" / "Borrow(unbound local)" /
                //     the `&mut` promoted-slot guards) — returning it, storing it, passing it
                //     by value all stay refused;
                //   * a CAPTURING or coroutine literal does not match the recognizer and falls
                //     through to `lower_expr`'s fail-closed closure arm below.
                if self.non_capturing_closure_literal(init) {
                    return;
                }
                // Trust (wave-22): `let _ = |…| {…}` / `let _ = async {…}` — a closure/coroutine
                // LITERAL bound to the WILDCARD pattern `_` (`binding_var` returns `None` only for a
                // non-`Binding` pattern, and a closure init admits only `_` or a binding) is a
                // DISCARDED temporary: immediately dropped, never named, never called/polled. Same
                // no-op-modulo-Drop argument as the bare-statement case in `Action::Expr`, now also
                // admitting CAPTURING and coroutine literals (the `non_capturing_closure_literal`
                // check above only covers a plain empty-capture closure). The gate is
                // `var.is_none()` — `binding_var` returns `None` for any non-`Binding` pattern, but
                // for a closure INIT that is exactly the wildcard `_`: a tuple/struct/ref/literal
                // pattern is a type error against `ty::Closure`, so `_` is the sole non-binding
                // shape reachable here. A real binding `let f = …` (`var.is_some()`) stays lowered so
                // a later `f()`/use is faithful (or fails closed at its own site — Wave B territory).
                if var.is_none() && self.closure_literal(init) {
                    return;
                }
                // The local's type is the init expression's type (Rust infers them equal). Snapshot it
                // before `lower_expr` borrows `self` mutably.
                let init_rty = self.thir.exprs[init].ty;
                if let Some(v) = self.lower_expr(init) {
                    if let Some(var) = var {
                        let ty = self.map_ty(init_rty);
                        if self.is_promoted(var) {
                            // Trust: a `&mut`-borrowed local — promote it to memory. `Alloca` a slot
                            // and `Store` the init value; reads/writes/`&mut` route through the slot.
                            // The init value itself must not be a borrow pointer (we do not promote a
                            // slot holding a pointer — `&mut r` where r is a borrow is out of scope).
                            if self.is_borrow_ptr(v) {
                                self.unsupported.push((
                                    format!("{:?}", self.thir.exprs[init].span),
                                    "Promote(init is borrow ptr)",
                                ));
                            } else if is_scalar_ty(&ty) {
                                self.alloc_promoted(var, ty, v);
                            } else if let Some(oty) = self.opaque_local_aggregate_ty(init_rty) {
                                // Trust (realbody store move-out): a `&mut` NON-scalar local whose type
                                // is a provably-OPAQUE-carrying aggregate (a struct `struct_ty_rmw_opaque`
                                // collapsed a non-pure sibling of — the real `let mut store =
                                // reflowed.store;` shape, `Store { lines: Vec, .. }` → `Ty::Struct[Ty::Unit,
                                // U64]`). We do NOT promote it to a scalar slot (unfaithful); bind it as an
                                // SSA local. Its ONLY sound consumer is a method-receiver `&mut store` —
                                // an opaque wave-MC `call @callee` (`Store::clear`) that sets
                                // `contains_call` → the body is NotRun (never interpreted/flipped). A real
                                // `&mut store` ARG still declines at its own `Borrow` site; a by-value read
                                // round-trips the opaque aggregate. `v` was read via the SAME opaque
                                // builder, so its runtime type and `oty` agree (`register_struct` dedups).
                                self.set_local(var, v, oty);
                                // Trust (wave-ER): joins the opaque-carrier ledger so a BY-VALUE
                                // read (`self.storage.pages = new_pages` — the whole-container
                                // write's RHS) round-trips the SSA value instead of declining at
                                // the promoted-slotless VarRef arm, and so the for-summary can
                                // HAVOC it. The receiver-carrier admission it also grants is one
                                // this local already had (the bare-local arm of
                                // `try_lower_receiver_place_value`).
                                if !self.opaque_carrier_locals.contains(&var) {
                                    self.opaque_carrier_locals.push(var);
                                }
                            } else if matches!(init_rty.kind(), ty::Adt(..))
                                && !is_pure_value_shape(&self.fat_shape(init_rty, &mut Vec::new()))
                            {
                                // Trust (wave-ER): a `&mut`-borrowed NON-pure aggregate local whose
                                // type even the registered-opaque channel above could not build — a
                                // std container ROOT (`let mut new_rows = Vec::with_capacity(…)`,
                                // the erase ring-rebuild). Same SSA-bind posture as the arm above,
                                // at the fully-opaque type `Ty::Unit` (the wave-EL enum-local
                                // treatment): no faithful scalar-slot model exists, so the local is
                                // bound as an opaque SSA unit and joins `opaque_carrier_locals`.
                                // Its sound consumers: a by-value read (round-trips the opaque
                                // value), the method-receiver value carrier
                                // (`try_lower_receiver_place_value` — `new_rows.push(row)`, NotRun
                                // basis), a whole-container lane write (which DISCARDS the value —
                                // the wave-ER Assign arm), or a for-summary HAVOC rebind. A real
                                // `&mut` ARG still declines at its own Borrow site; a PURE-value
                                // struct (`Range<u16>` — a faithful scalar-slot/value model would
                                // exist) keeps declining below, never silently opaqued.
                                self.set_local(var, v, Ty::Unit);
                                if !self.opaque_carrier_locals.contains(&var) {
                                    self.opaque_carrier_locals.push(var);
                                }
                            } else {
                                self.unsupported.push((
                                    format!("{:?}", self.thir.exprs[init].span),
                                    "Promote(non-scalar &mut local)",
                                ));
                            }
                        } else {
                            // `let [mut] y = init` binds (or, for `mut`, initial-binds) the local. Same
                            // mechanism as a later `y = …` reassignment — both rebind via `set_local`.
                            self.set_local(var, v, ty);
                        }
                    }
                }
            }
            Action::Let(_, None) => {}
            Action::LetDestructure(node, init) => {
                // Trust (wave-LD): `let <destructure> = init;`. Lower the init ONCE, then bind each
                // leaf via `ExtractField` chains. If the init fails to lower (records its own gap) the
                // leaves stay unbound and fall closed at their uses — same fail-closed outcome as before
                // this wave, never a regression (a compound-destructure let bound NOTHING previously).
                let init_rty = self.thir.exprs[init].ty;
                if let Some(v) = self.lower_expr(init) {
                    // Map the init's aggregate type, but SPECULATIVELY: pre-wave this `let` routed to
                    // `Action::Let(None, init)`, which lowered the init and — because its `map_ty` was
                    // gated behind `if let Some(var)` — NEVER mapped the init type when the pattern bound
                    // no single var. So if `map_ty` DECLINES here (pushes a tag: a `f16`/`f128` element,
                    // a recursive/ptr-payload enum, an unregisterable struct field, …) we must not let
                    // that tag dirty a body that lowered clean before. Roll the tag back and fall back to
                    // the exact pre-wave behaviour: init lowered for effects, leaves left UNBOUND (each
                    // USE then fails closed at its own site with `VarRef(unbound)`, precisely as before).
                    // This keeps `became_dirty == 0` — a body clean pre-wave (all leaves unused) stays
                    // clean; a body dirty pre-wave (a used leaf) stays dirty for the same reason.
                    let mark = self.unsupported.len();
                    let root_ty = self.map_ty(init_rty);
                    if self.unsupported.len() != mark {
                        self.unsupported.truncate(mark);
                    } else {
                        // `emit_bind` pushes no tags (only `set_local`/`ExtractField`/registry reads);
                        // returning `false` means the value shape was not `ExtractField`-able (impossible
                        // for well-typed THIR whose pattern is a `Fields` destructure over a cleanly
                        // mapped aggregate). Any leaf it did bind is the exact field value, so a partial
                        // bind is still sound and the unbound remainder falls closed at its use sites.
                        let _ = self.emit_bind(&node, v, root_ty);
                    }
                }
            }
            // Trust (wave-TD, 2026-07-14): the plain TUPLE DESTRUCTURE — closes the
            // measured cross-fn seam gap (the real consumer `let (_seq, evicted) =
            // self.log.append_at(op, ts);`, aterm-gui temporal.rs:126, which declined
            // as unbound-binding fallout: the init call lowered, the components never
            // bound, so every use tagged `VarRef(unbound)` / took an unsupported-cond
            // branch). The initializer lowers FIRST (its effects — the call — are kept
            // exactly as the pre-wave fallthrough kept them); each BOUND component then
            // binds to an `ExtractField` of the init value at the component's mapped
            // type. FAIL-CLOSED, never silent:
            //   * a non-tuple mapped type / arity drift tags `LetTuple(non-tuple mapped
            //     ty)` / `LetTuple(arity mismatch)` and leaves the binds unbound (the
            //     pre-wave posture — every use still fails closed at its own site);
            //   * a `&mut`-borrowed (promoted) component tags `LetTuple(promoted
            //     binding)` and stays unbound (the promoted-slot guards refuse its uses);
            //   * nested / by-ref / non-tuple patterns never reach here
            //     (`tuple_pat_bindings` returns `None` → the pre-wave fallthrough).
            // LEDGER (the wave-SEAM `option_lane_values` TUPLE-PROJECTION case): a bound
            // component whose rustc type is an opaque-lane `Option` (the flag's
            // `Ty::Bool` mapping) is a PROVEN discriminant iff the initializer peels to
            // a call of a LOCAL `FnDef` — the same admission as the direct local-callee
            // Option result (a local callee's declaration carries `lower_fn`'s mapped
            // signature, so its returned tuple's lane component IS the discriminant
            // bool; an extern/std callee's components are deliberately NOT ledgered —
            // the downstream value-lane test fails closed on them, pre-wave verbatim).
            Action::LetTuple(binds, Some(init)) => {
                let init_rty = self.thir.exprs[init].ty;
                // The ledger's local-callee admission, computed BEFORE lowering.
                let init_is_local_call = {
                    let mut e = init;
                    loop {
                        match &self.thir.exprs[e].kind {
                            ExprKind::Scope { value, .. } => e = *value,
                            ExprKind::Use { source } => e = *source,
                            _ => break,
                        }
                    }
                    match &self.thir.exprs[e].kind {
                        ExprKind::Call { fun, .. } => {
                            let mut f = *fun;
                            loop {
                                match &self.thir.exprs[f].kind {
                                    ExprKind::Scope { value, .. } => f = *value,
                                    ExprKind::Use { source } => f = *source,
                                    _ => break,
                                }
                            }
                            matches!(self.thir.exprs[f].ty.kind(),
                                ty::FnDef(did, _) if did.is_local())
                        }
                        _ => false,
                    }
                };
                let span = self.thir.exprs[init].span;
                let Some(v) = self.lower_expr(init) else { return };
                let ty::Tuple(comp_rtys) = init_rty.kind() else {
                    // tuple_pat_bindings admits only ty::Tuple patterns, and Rust types
                    // the init equal to the pattern — defensive, fail-closed.
                    self.unsupported.push((format!("{span:?}"), "LetTuple(non-tuple init ty)"));
                    return;
                };
                let Ty::Tuple(comp_tys) = self.map_ty(init_rty) else {
                    self.unsupported.push((format!("{span:?}"), "LetTuple(non-tuple mapped ty)"));
                    return;
                };
                if comp_tys.len() != comp_rtys.len() || binds.len() != comp_tys.len() {
                    self.unsupported.push((format!("{span:?}"), "LetTuple(arity mismatch)"));
                    return;
                }
                for (idx, slot) in binds.iter().enumerate() {
                    let Some(var) = slot else { continue };
                    if self.is_promoted(*var) {
                        self.unsupported.push((format!("{span:?}"), "LetTuple(promoted binding)"));
                        continue;
                    }
                    let cty = comp_tys[idx].clone();
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::ExtractField {
                            ty: cty.clone(),
                            aggregate: v,
                            field: u32::try_from(idx).expect("tuple arity fits u32"),
                        })
                        .with_result(res),
                    );
                    self.set_local(*var, res, cty);
                    if init_is_local_call
                        && option_flag_lanes_enabled()
                        && matches!(comp_rtys[idx].kind(), ty::Adt(a, _)
                            if self.tcx.get_diagnostic_item(rustc_span::sym::Option)
                                == Some(a.did()))
                        && self.is_opaque_lane_enum(comp_rtys[idx])
                    {
                        self.option_lane_values.push(res);
                    }
                }
            }
            Action::LetTuple(_, None) => {}
            Action::LetElse(binds, variant_test, init, else_blk, pat_span) => {
                // Defensive: rustc requires a let-`else` initializer.
                let Some(init) = init else {
                    self.unsupported.push((pat_span, "LetElse(no initializer)"));
                    return;
                };
                // The TEST half rides the same admission as a `let`-chain condition
                // (`lower_let_opaque_test`): an OPAQUE (non-pure) enum scrutinee, by-value
                // variant bindings, opaque `Undef Bool` result, `contains_call` forced. Any
                // inadmissible shape fails closed HERE — never a silently-dropped else arm.
                let init_span = self.thir.exprs[init].span;
                let Some(test) = self.lower_let_opaque_test(init_span, init, binds, variant_test)
                else {
                    self.unsupported.push((pat_span, "LetElse(unsupported)"));
                    return;
                };
                // CFG: `cond_br %test -> cont, else` — the else block must DIVERGE (rustc
                // types it `!`), the continuation carries the (already-bound) pattern vars.
                let else_id = self.fresh_block_id();
                let cont_id = self.fresh_block_id();
                self.seal_with(Inst::CondBr {
                    cond: test,
                    then_target: cont_id,
                    then_args: vec![],
                    else_target: else_id,
                    else_args: vec![],
                });
                self.start_block(else_id, vec![]);
                let (blk_stmts, tail) = {
                    let blk = &self.thir.blocks[else_blk];
                    (blk.stmts.iter().copied().collect::<Vec<StmtId>>(), blk.expr)
                };
                for s in blk_stmts {
                    self.lower_stmt(s);
                    if self.sealed {
                        break;
                    }
                }
                if !self.sealed {
                    if let Some(t) = tail {
                        let _ = self.lower_expr(t);
                    }
                }
                if !self.sealed {
                    // rustc guarantees the else block diverges; an open end means some
                    // construct inside failed to lower its divergence — fail closed (the tag
                    // keeps the body out of the splice) and seal defensively so no block is
                    // left dangling-open.
                    self.unsupported.push((pat_span, "LetElse(else did not diverge)"));
                    self.seal_with(Inst::Unreachable);
                }
                self.start_block(cont_id, vec![]);
            }
        }
    }

    /// Trust: current SSA value bound to `var` (last-write-wins, so the most recent `let`/assignment
    /// wins). `None` if the local is unbound in the current environment.
    fn local_value(&self, var: LocalVarId) -> Option<ValueId> {
        self.locals.iter().rev().find(|(v, _)| *v == var).map(|(_, val)| *val)
    }

    /// Trust: the (interpretable) `trust_ir::Ty` of a local. A Rust local has ONE type across all its
    /// reassignments, so this is recorded once (first bind) and never changes. Used to type the join
    /// block-param the merge machinery adds for a local mutated inside an `if`/`match` arm.
    fn local_ty(&self, var: LocalVarId) -> Option<Ty> {
        self.local_tys.iter().rev().find(|(v, _)| *v == var).map(|(_, t)| t.clone())
    }

    /// Trust: (re)bind `var` to `val`. Append-only last-write-wins — a fresh `let` (shadowing), a
    /// `y = …` reassignment, and a join block-param rebind all push a new pair, and `local_value`
    /// reads the latest. The pre-split snapshot the merge machinery captures is a plain clone of the
    /// whole `locals` vec, so an arm's pushes never leak past the snapshot restore. `ty` is the
    /// local's declared `trust_ir::Ty`, recorded once (the first time the local is bound) so a later
    /// `if`/`match`-arm merge can type the local's join block-param.
    fn set_local(&mut self, var: LocalVarId, val: ValueId, ty: Ty) {
        if self.local_ty(var).is_none() {
            self.local_tys.push((var, ty));
        }
        self.locals.push((var, val));
    }

    /// Trust (wave-LD): emit the binding of an irrefutable `let`-destructure plan (`BindNode`) against
    /// `val` (of mapped type `val_ty`). Each `Fields` node reads its live subfields with a LOGICAL
    /// `ExtractField` (declaration/position index — the same convention the tuple/struct MATCH path
    /// uses; no byte offsets) and recurses; each `Bind` leaf `set_local`s. Returns `true` if the whole
    /// plan bound successfully; `false` fails CLOSED (a leaf whose enclosing aggregate did not map to a
    /// tuple/struct — impossible for well-typed THIR, but guarded) leaving already-bound leaves correct
    /// and unbound leaves to fall closed at their own use sites. Every value it DOES bind is the exact
    /// `ExtractField` of the correct field, so no partial state is ever unsound.
    fn emit_bind(&mut self, node: &BindNode, val: ValueId, val_ty: Ty) -> bool {
        match node {
            BindNode::Skip => true,
            BindNode::Bind(var, inner) => {
                // A `&mut`-borrowed destructured local (`let (mut a, b) = t; let r = &mut a;`) is
                // PROMOTED to a memory slot by `collect_mut_borrowed`, which needs an `Alloca`+`Store`
                // (not an SSA `set_local`) so a write through the `&mut` is visible to later reads. That
                // memory-slot binding is out of scope for this wave — fail closed (the promoted local
                // stays unbound; its `&mut a` use then tags at its own site with the existing
                // promoted-slot reason, exactly as pre-wave when NO destructure local bound). Any leaf
                // already bound stays correct (a partial bind is sound).
                if self.is_promoted(*var) {
                    return false;
                }
                self.set_local(*var, val, val_ty.clone());
                match inner {
                    Some(sub) => self.emit_bind(sub, val, val_ty),
                    None => true,
                }
            }
            BindNode::Fields(fields) => {
                // The aggregate we extract from must have mapped to a tuple/struct. `map_ty` lowers
                // tuples, fixed arrays (N>0), and structs to these shapes; anything else (scalar, ptr,
                // enum) is not `ExtractField`-able → fail closed.
                let elem_tys = match &val_ty {
                    Ty::Tuple(elem_tys) => elem_tys.clone(),
                    Ty::Struct(sid) => match self.registered_struct_field_tys(*sid) {
                        Some(f) => f,
                        None => return false,
                    },
                    _ => return false,
                };
                for (idx, sub) in fields {
                    // Skip the ExtractField for a subtree that binds nothing (`_`) — the read would be
                    // dead, and eliding it keeps the emitted IR minimal (no dead-store flip hazard).
                    if !bind_node_binds(sub) {
                        continue;
                    }
                    let Some(fty) = elem_tys.get(*idx as usize).cloned() else {
                        return false;
                    };
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::ExtractField {
                            ty: fty.clone(),
                            aggregate: val,
                            field: *idx,
                        })
                        .with_result(res),
                    );
                    if !self.emit_bind(sub, res, fty) {
                        return false;
                    }
                }
                true
            }
        }
    }

    /// Recursive THIR walk. Appends to the currently-open block (`self.cur`).
    /// Returns the `ValueId` holding the result (None for stmts/diverging/unit).
    /// Fail-closed: unhandled variants are recorded, never mis-lowered.
    /// Trust (C2-spans): mirror of [`Module::intern_file`] over the per-body table.
    fn intern_file(&mut self, path: &str) -> u32 {
        if let Some(i) = self.files.iter().position(|p| p == path) {
            return u32::try_from(i).expect("file table exceeds u32");
        }
        let idx = u32::try_from(self.files.len()).expect("file table exceeds u32");
        self.files.push(path.to_string());
        idx
    }

    /// Trust (C2-spans): rustc `Span` -> trust-ir `SourceSpan` ({file,line,col}, LO edge).
    /// Macro spans degrade to the call site (`source_callsite`, the span_map.rs precedent);
    /// dummy spans yield `None` rather than a fabricated location.
    fn to_source_span(&mut self, sp: rustc_span::Span) -> Option<SourceSpan> {
        let sp = sp.source_callsite();
        if sp.is_dummy() {
            return None;
        }
        let loc = self.tcx.sess.source_map().lookup_char_pos(sp.lo());
        // `prefer_local_unconditionally` is this tree's canonical filename rendering — the same
        // call `trust_verify` uses for obligation locations and trust-ir's own `span_map.rs`
        // uses for its file table, so the three lanes agree on file identity.
        let file = loc.file.name.prefer_local_unconditionally().to_string();
        let file = self.intern_file(&file);
        Some(SourceSpan {
            file,
            line: u32::try_from(loc.line).unwrap_or(u32::MAX),
            col: u32::try_from(loc.col.0).unwrap_or(u32::MAX),
        })
    }

    /// Trust (C2-spans): the ONLY instruction-emission chokepoint — stamps `cur_span`. Every
    /// former `self.push_node(InstrNode::new(..))` site (170 at conversion) goes through here.
    fn push_node(&mut self, mut node: InstrNode) {
        node.span = self.cur_span;
        self.cur.push(node);
    }

    /// Trust (C2-spans): span-scoping wrapper — the walk itself is `lower_expr_walk`. A wrapper
    /// rather than per-return restoration because the walk has dozens of early returns; nesting
    /// restores the parent's span on exit, recursion re-enters through here.
    fn lower_expr(&mut self, id: ExprId) -> Option<ValueId> {
        let saved = self.cur_span;
        self.cur_span = self.to_source_span(self.thir.exprs[id].span).or(saved);
        let r = self.lower_expr_walk(id);
        self.cur_span = saved;
        r
    }

    fn lower_expr_walk(&mut self, id: ExprId) -> Option<ValueId> {
        let expr: &Expr<'tcx> = &self.thir.exprs[id];
        // Snapshot the Copy fields we need after `&mut self` calls.
        let expr_ty = expr.ty;
        let expr_span = expr.span;
        match &expr.kind {
            // Trust: a `Scope` directly wrapping a `Loop` carries the loop's `HirId` in `hir_id`. The
            // break/continue label rustc emits for that loop is `region::Scope { local_id:
            // <loop hir_id>.local_id, data: Node }` (see `thir/cx/expr.rs`), so we capture it here and
            // hand it to `lower_loop` as the EXACT scope a `break`/`continue` inside the body targets —
            // robust against the body's structure (no need to scavenge a label out of the THIR tree).
            ExprKind::Scope { value, hir_id, .. } => {
                let hir_id = *hir_id;
                let value = *value;
                if let ExprKind::Loop { body } = &self.thir.exprs[value].kind {
                    let body = *body;
                    let loop_scope =
                        region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node };
                    return self.lower_loop(expr_span, loop_scope, body);
                }
                self.lower_expr(value)
            }
            ExprKind::Use { source } => self.lower_expr(*source),
            // Trust: `NeverToAny { source }` is the coercion of a `!`-typed (diverging) expression —
            // `break`, `continue`, `return`, a `!`-returning call — to some other type. It is
            // control-flow-transparent: lower the diverging `source` (which seals the current block via
            // its own terminator) and produce no value. Without this, the desugared `while`'s
            // `else { break }` arm (its `break` is wrapped in `NeverToAny`) hits the fail-closed
            // catch-all and the break never lowers, so the else-arm falls through to the loop body's
            // join instead of the exit — an infinite loop.
            ExprKind::NeverToAny { source } => self.lower_expr(*source),
            ExprKind::Block { block } => {
                // Copy out stmt ids + tail (Copy) so no `self.thir` borrow is held while lowering.
                let blk = &self.thir.blocks[*block];
                let stmts: Vec<StmtId> = blk.stmts.iter().copied().collect();
                let tail = blk.expr;
                for s in stmts {
                    self.lower_stmt(s);
                    // A statement may have diverged (`return;`). Once sealed, the rest is dead.
                    if self.sealed {
                        return None;
                    }
                }
                tail.and_then(|t| self.lower_expr(t))
            }
            // Trust (wave-CE): a captured-variable READ inside a capturing Fn/FnMut closure body.
            // The env param (`_0` / `ValueId(0)`, a `&{closure}` thin ptr) points at the closure
            // struct whose fields ARE the captures in `upvar_tys()` order. Model that struct as a
            // `Ty::Tuple(upvar_tys)` (capture order = field index) and read capture `i` by Loading
            // the tuple through the env ptr + `ExtractField i` (the wave-11 aggregate-Load-through-ref
            // pattern). A by-REF capture (field is a thin `Ty::Ptr` — the common non-`move` case)
            // then `Load`s the scalar value through that field. CLEAN-ONLY: a struct-Load through the
            // env param → the shim fails closed → never flips; the env-param read → `NotRun` → never
            // interpreted. FAIL CLOSED on: a FnOnce-by-value / coroutine env (pointee not
            // `ty::Closure`), a disjoint/projected capture (≠ exactly one whole-variable capture), a
            // non-thin capture (only scalar / thin `Ty::Ptr` fields — keeps the env tuple spliceable),
            // or an unresolved capture kind (field type neither the value type nor a thin ptr to it).
            ExprKind::UpvarRef { closure_def_id, var_hir_id } => {
                let closure_def_id = *closure_def_id;
                let var_hir_id = *var_hir_id;
                let Some(cl_def) = closure_def_id.as_local() else {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "UpvarRef(non-local closure)"));
                    return None;
                };
                // The env must be a Fn/FnMut `&{closure}` (the pat-less param 0); its pointee is the
                // closure type carrying the capture list. A FnOnce-by-value env (`ty::Closure` by
                // value) / coroutine env do NOT match the `ty::Ref` → `ty::Closure` shape below.
                // Trust (B6, v25 Fn/ByValue slice): `by_value_env = true` means the env param
                // IS the closure value itself (FnOnce) — signed `Ty::Closure(id)` by
                // `closure_env_param_ty` — and the capture is a DIRECT `ExtractField` on
                // `ValueId(0)` (register-level; the interpreter's B6 closure field arms).
                // No memory transit, no Load.
                let (closure_ty, by_value_env) = match self.thir.params.raw.first() {
                    Some(p) if p.pat.is_none() => match p.ty.kind() {
                        ty::Ref(_, pointee, _) => (*pointee, false),
                        ty::Closure(..) => (p.ty, true),
                        _ => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "UpvarRef(non-Fn env)"));
                            return None;
                        }
                    },
                    _ => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "UpvarRef(missing env param)"));
                        return None;
                    }
                };
                let ty::Closure(_, cargs) = closure_ty.kind() else {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "UpvarRef(non-closure env pointee)"));
                    return None;
                };
                let upvar_tys = cargs.as_closure().upvar_tys();
                // Resolve the capture INDEX: EXACTLY ONE whole-variable capture for this var
                // (`get_root_variable` matches the root hir id; an empty projection = the whole var —
                // a disjoint `x.field` capture has a non-empty projection and fails closed, as does a
                // var captured under two disjoint projections).
                let captures = self.tcx.closure_captures(cl_def);
                let mut index: Option<usize> = None;
                let mut ambiguous = false;
                for (i, cap) in captures.iter().enumerate() {
                    if cap.get_root_variable() == var_hir_id.0 && cap.place.projections.is_empty() {
                        if index.is_some() {
                            ambiguous = true;
                        }
                        index = Some(i);
                    }
                }
                let (Some(index), false) = (index, ambiguous) else {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "UpvarRef(disjoint/projected capture)"));
                    return None;
                };
                if index >= upvar_tys.len() {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "UpvarRef(capture index OOB)"));
                    return None;
                }
                // Map every capture type; gate ALL thin (scalar or `Ty::Ptr`) so the env tuple is
                // table-free/spliceable and the field read is well-formed. A fat/aggregate/Drop
                // capture fails closed here.
                let elem_tys: Vec<Ty> = upvar_tys.iter().map(|t| self.map_ty(t)).collect();
                if !elem_tys.iter().all(|t| is_scalar_ty(t) || matches!(t, Ty::Ptr)) {
                    self.unsupported.push((format!("{expr_span:?}"), "UpvarRef(non-thin capture)"));
                    return None;
                }
                let field_ty = elem_tys[index].clone();
                let upvar_ref_ty = self.map_ty(expr_ty);
                let env = ValueId::new(0);
                let agg = if by_value_env {
                    // Trust (B6): the env param IS the closure value — the aggregate to
                    // field-read is `ValueId(0)` itself. Its signed type must be the
                    // first-class `Ty::Closure` (the same `map_ty` split the signature
                    // took); anything else means the signature lane declined — fail
                    // closed rather than field-read a Unit placeholder.
                    if !matches!(self.map_ty(closure_ty), Ty::Closure(_)) {
                        self.unsupported.push((format!("{expr_span:?}"), "UpvarRef(non-Fn env)"));
                        return None;
                    }
                    env
                } else {
                    // Load the closure struct (tuple) through the env ptr (`ValueId(0)`).
                    let env_tuple = Ty::Tuple(elem_tys);
                    let agg = self.fresh();
                    self.push_node(InstrNode::new(Inst::Load {
                            ty: env_tuple,
                            ptr: env,
                            volatile: false,
                            align: None,
                        })
                        .with_result(agg),
                    );
                    agg
                };
                let field = self.fresh();
                self.push_node(InstrNode::new(Inst::ExtractField {
                        ty: field_ty.clone(),
                        aggregate: agg,
                        field: index as u32,
                    })
                    .with_result(field),
                );
                // Capture kind (comparison-based, type-correct either way): by-VALUE (the field IS the
                // value) or by-REF (the field is a thin `Ty::Ptr`; `Load` the scalar value through it).
                if field_ty == upvar_ref_ty {
                    return Some(field);
                }
                if field_ty == Ty::Ptr && is_scalar_ty(&upvar_ref_ty) {
                    let v = self.fresh();
                    self.push_node(InstrNode::new(Inst::Load {
                            ty: upvar_ref_ty,
                            ptr: field,
                            volatile: false,
                            align: None,
                        })
                        .with_result(v),
                    );
                    return Some(v);
                }
                self.unsupported
                    .push((format!("{expr_span:?}"), "UpvarRef(capture kind unresolved)"));
                return None;
            }
            ExprKind::VarRef { id } => {
                let id = *id;
                // Trust: a PROMOTED local lives in a memory slot — read it with a `Load` so a prior
                // write-through-`&mut` (`*r = v`, an `Inst::Store` to the same slot) is observed.
                if self.is_promoted(id) {
                    // Trust (wave-ER): an OPAQUE-CARRIER local is promoted-but-slotless BY
                    // DESIGN (bound as an SSA `Ty::Unit` — no faithful slot model exists). A
                    // by-value read yields its current SSA value: the opaque value round-trips
                    // (its only consumers are the opaque carriers / a discarding container
                    // write), and any write-through-`&mut` it may have suffered happened inside
                    // an opaque callee or a summarized loop — both NotRun channels whose
                    // post-state the summary already HAVOCS. Any other promoted-but-slotless
                    // local keeps the fail-closed tag below.
                    if self.opaque_carrier_locals.contains(&id) && self.promoted_slot(id).is_none()
                    {
                        if let Some(v) = self.local_value(id) {
                            if !self.is_borrow_ptr(v) {
                                return Some(v);
                            }
                        }
                    }
                    let (slot, ty) = match (self.promoted_slot(id), self.promoted_ty(id)) {
                        (Some(s), Some(t)) => (s, t),
                        _ => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "VarRef(promoted slot missing)"));
                            return None;
                        }
                    };
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Load { ty, ptr: slot, volatile: false, align: None })
                            .with_result(res),
                    );
                    return Some(res);
                }
                // Last-write-wins lookup (handles `let` shadowing AND `mut` reassignment — both
                // rebind via `set_local`, so the latest version is what a use sees).
                match self.local_value(id) {
                    Some(val) => Some(val),
                    None => {
                        // Trust (wave-UV): a read of a genuinely UNIT-typed (`()`) local is a
                        // value-less no-op, NOT a failure. The producer models unit as
                        // non-value-producing everywhere (the interpreter cannot materialize a
                        // `Ty::Unit` value — see the join-shape `value_producing` gates), so
                        // `let y: () = ()` never binds the local (`lower_expr(())` returns `None`
                        // WITHOUT a tag). A later `let _ = y` reads it and yields the unit value =
                        // no value: return `None` WITHOUT a tag, exactly like any other unit
                        // expression. Every value-NEEDING consumer (a call arg, an aggregate field)
                        // independently fails closed on the `None` at its own site, so this never
                        // masks a real value. Gate on the REAL rustc unit type
                        // (`ty::Tuple(empty)`), NOT `map_ty(...) == Ty::Unit` — the latter is also
                        // the fail-closed placeholder for degraded/unsupported types, and silencing
                        // those WOULD mask an unsupported non-unit value as clean.
                        if matches!(expr_ty.kind(), ty::Tuple(elems) if elems.is_empty()) {
                            return None;
                        }
                        self.unsupported.push((format!("{expr_span:?}"), "VarRef(unbound)"));
                        None
                    }
                }
            }
            ExprKind::Literal { lit, neg } => {
                if let LitKind::Int(v, _) = lit.node {
                    let ty = self.map_ty(expr_ty);
                    let Some((bits, signed)) = int_scalar_bits(&ty) else {
                        self.unsupported.push((format!("{expr_span:?}"), "Literal(non-int Ty)"));
                        return None;
                    };
                    let value = integer_literal_constant(v.get(), *neg, signed, bits);
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty, value }).with_result(res));
                    Some(res)
                } else if let LitKind::Bool(b) = lit.node {
                    // `true` / `false` — common in `if`/`&&`/`||` arms. `neg` never applies to bool.
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(b) })
                            .with_result(res),
                    );
                    Some(res)
                } else if let LitKind::Char(c) = lit.node {
                    // Trust (B1): a char literal — first-class `Ty::Char` carrying its Unicode
                    // code point as 32 unsigned bits, matching the faithful MIR extraction
                    // without collapsing the type to `U32`. `neg` never applies to char.
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: Ty::Char,
                            value: Constant::Int(c as u32 as i128),
                        })
                        .with_result(res),
                    );
                    Some(res)
                } else if let LitKind::Float(sym, _) = lit.node {
                    // Trust: a float literal → `Constant::Float` under the `map_ty` F32/F64
                    // convention. The literal TYPE comes from `expr_ty` (typeck's inference,
                    // covering both suffixed `1.5f32` and unsuffixed `1.5` literals), not the
                    // suffix. PARSE EXACTNESS: rustc evaluates the MIR constant with
                    // `rustc_apfloat` (correctly-rounded IEEE-754 nearest-even,
                    // `parse_float_into_scalar`); Rust's `str::parse::<f32/f64>` is likewise
                    // correctly rounded (Eisel–Lemire), so the bit patterns agree on every
                    // valid literal — including overflow-to-infinity (`1e999`) and subnormals.
                    // Underscore separators are part of the THIR symbol but not the float
                    // grammar `parse` accepts; strip them first (rustc's own parse does too).
                    // `neg` negates AFTER parsing (matching `parse_float_into_scalar(neg)`),
                    // so `-0.0` keeps its sign bit. An f32 value round-trips exactly through
                    // the `Constant::Float(f64)` carrier: f64 superset-represents every f32,
                    // and the interpreter converts back via `value as f32` (bit-exact here).
                    // FAIL-CLOSED: an f16/f128 literal (its `map_ty` already recorded
                    // `Ty(float-width)`) or an unparseable symbol — precise tag, no guess.
                    let ty = self.map_ty(expr_ty);
                    let stripped = sym.as_str().replace('_', "");
                    let value: Option<f64> = match ty {
                        Ty::F32 => stripped
                            .parse::<f32>()
                            .ok()
                            .map(|v| f64::from(if *neg { -v } else { v })),
                        Ty::F64 => stripped.parse::<f64>().ok().map(|v| if *neg { -v } else { v }),
                        _ => None,
                    };
                    match value {
                        Some(v) => {
                            let res = self.fresh();
                            self.push_node(InstrNode::new(Inst::Const { ty, value: Constant::Float(v) })
                                    .with_result(res),
                            );
                            Some(res)
                        }
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Literal(float unsupported)"));
                            None
                        }
                    }
                } else if let LitKind::Byte(b) = lit.node {
                    // Trust (wave-17): a byte literal `b'z'` — always type `u8` — is a plain
                    // `Ty::U8` constant (the trivial near-miss of the string/byte-literal blocker;
                    // no global, no pointer). `neg` never applies to a byte literal.
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(b as i128) })
                            .with_result(res),
                    );
                    Some(res)
                } else if let LitKind::Str(sym, _) = lit.node {
                    // Trust (wave-17, respelled B2-2): a string literal `"abc"` — type
                    // `&'static str`. Materialize its UTF-8 bytes as a `[u8; N]` module
                    // GLOBAL (`emit_bytes_global`) and assemble the FIRST-CLASS fat
                    // pointer via the FORMAT's own constructor: `PtrFromParts { ptr_ty:
                    // FatPtr(Str), metadata_ty: U64, data, metadata: len }` — matching
                    // `map_ty(&str)` and the oracle's faithful-lane spelling. The fat
                    // value flows through the ordinary value paths (the `data_ptr` is
                    // consumed by `PtrFromParts`, never itself returned). FAIL CLOSED on
                    // the empty string (a zero-length array global is not proven
                    // faithful end-to-end).
                    let bytes: Vec<u8> = sym.as_str().as_bytes().to_vec();
                    match self.emit_bytes_global(&bytes) {
                        Some(data_ptr) => {
                            let len_val = self.fresh();
                            self.push_node(InstrNode::new(Inst::Const {
                                    ty: Ty::U64,
                                    value: Constant::Int(bytes.len() as i128),
                                })
                                .with_result(len_val),
                            );
                            let fat_ty = Ty::FatPtr(trust_ir::FatPtrKind::Str);
                            let fat = self.fresh();
                            self.push_node(InstrNode::new(Inst::PtrFromParts {
                                    ptr_ty: fat_ty,
                                    metadata_ty: Ty::U64,
                                    data: data_ptr,
                                    metadata: len_val,
                                })
                                .with_result(fat),
                            );
                            Some(fat)
                        }
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Literal(non-int/bool)"));
                            None
                        }
                    }
                } else if let LitKind::ByteStr(bytes_sym, _) = lit.node {
                    // Trust (wave-17): a byte-string literal `b"abc"` — type `&'static [u8; N]`, a
                    // reference to a SIZED array. Materialize the same `[u8; N]` bytes GLOBAL but
                    // return the THIN `GlobalAddr` pointer (`Ty::Ptr`), NOT a fat tuple: the length
                    // lives in the array TYPE, not a separate lane. Gate on the mapped expr type —
                    // it is `Ty::Ptr` for `&[u8; N]` (a thin ref to a sized array); a fat
                    // `Ty::Tuple([Ptr, I64])` target (an already-unsized `&[u8]`, which a bare
                    // literal never has — coercion wraps the literal in a separate node) is NOT
                    // emitted here and FAILS CLOSED. Register the `'static` address like the wave-16
                    // promoted-borrow path (`borrow_ptrs` + `global_ptrs`) so returning it is
                    // admitted while every other borrow-ptr escape stays fail-closed. FAIL CLOSED on
                    // the empty byte string (zero-length global).
                    if matches!(self.map_ty(expr_ty), Ty::Ptr) {
                        match self.emit_bytes_global(bytes_sym.as_byte_str()) {
                            Some(data_ptr) => {
                                self.borrow_ptrs.push(data_ptr);
                                self.global_ptrs.push(data_ptr);
                                Some(data_ptr)
                            }
                            None => {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Literal(non-int/bool)"));
                                None
                            }
                        }
                    } else {
                        self.unsupported.push((format!("{expr_span:?}"), "Literal(non-int/bool)"));
                        None
                    }
                } else {
                    // CStr, LitKind::Err, and any future non-int/bool/char/float/str/byte literal.
                    self.unsupported.push((format!("{expr_span:?}"), "Literal(non-int/bool)"));
                    None
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                // Operand type decides signedness + the compared `Ty` for `ICmp`.
                let lhs_rty = self.thir.exprs[*lhs].ty;
                // Trust: the RHS's rustc type, needed by the shift-amount range check (the shift
                // amount may have a different integer type than the shifted value).
                let rhs_rty = self.thir.exprs[*rhs].ty;
                let l = self.lower_expr(*lhs)?;
                let r = self.lower_expr(*rhs)?;
                // Fail-closed: a borrow pointer must not feed a binary op (pointer arithmetic /
                // comparison is not modeled by this foothold; the interpreter rejects it anyway).
                if self.is_borrow_ptr(l) || self.is_borrow_ptr(r) {
                    self.unsupported.push((format!("{expr_span:?}"), "Binary(borrow ptr operand)"));
                    return None;
                }
                let signed = matches!(lhs_rty.kind(), ty::Int(_));
                // Trust: FLOAT comparison → `Inst::FCmp`, never `ICmp` (an integer compare over
                // IEEE bit patterns would order negatives/NaN wrongly). The op table is
                // byte-for-byte the MIR-side oracle's `map_float_binop` (trust-ir-bridge
                // lower.rs:362-367): ORDERED for `==`/`<`/`<=`/`>`/`>=` (false on any NaN
                // operand) and UNORDERED for `!=` (true on any NaN operand) — exactly Rust's
                // IEEE-754 comparison semantics. Float ARITHMETIC falls through to
                // `emit_arith_binop`, whose float arm emits the trap-free `FAdd`-family op.
                if matches!(lhs_rty.kind(), ty::Float(_)) {
                    if let Some(fcmp) = map_fcmp(*op) {
                        let ty = self.map_ty(lhs_rty);
                        if !matches!(ty, Ty::F32 | Ty::F64) {
                            // f16/f128 — `map_ty` already recorded the precise width gap.
                            return None;
                        }
                        let res = self.fresh();
                        self.push_node(InstrNode::new(Inst::FCmp { op: fcmp, ty, lhs: l, rhs: r })
                                .with_result(res),
                        );
                        return Some(res);
                    }
                } else if let Some(icmp) = map_icmp(*op, signed) {
                    let ty = self.map_ty(lhs_rty);
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::ICmp { op: icmp, ty, lhs: l, rhs: r })
                            .with_result(res),
                    );
                    return Some(res);
                }
                // Trust: all non-comparison binary ops route through the shared MIR-faithful
                // emitter (`Inst::Overflow`+`Assert` for checked `+`/`-`/`*`, the unconditional
                // div/rem zero + signed MIN/-1 asserts, the checked shift-amount assert, plain
                // wrapping `BinOp` otherwise) — the same emitter `ExprKind::AssignOp` uses, so
                // `a / b` and `a /= b` trap on exactly the same inputs.
                let ty = self.map_ty(expr_ty);
                self.emit_arith_binop(expr_span, *op, ty, signed, rhs_rty, l, r)
            }
            ExprKind::Call { fun, args, from_hir_call, .. } => {
                // Trust: SLICE `s.len()` — the `<[T]>::len(&self) -> usize` lang-item method. rustc
                // lowers it to a `Call` to the `slice_len_fn` lang item with the slice fat pointer as
                // the sole receiver argument. We recognize it and read the LENGTH lane directly:
                // `ExtractField(slice, 1)` yields the `I64` len, cast to the `usize`-mapped result type.
                // This is FAITHFUL (the len is the real static length stored in the fat pointer by the
                // `Unsize` coercion) and keeps the body interpretable (no cross-module `Call`).
                if let Some(v) =
                    self.try_lower_slice_len(expr_span, expr_ty, *fun, args, *from_hir_call)
                {
                    return Some(v);
                }
                // Trust (wave-N): `core::mem::offset_of!(C, field)` — rustc lowers each field level to
                // a synthetic `Call` to the `OffsetOf` lang-item intrinsic; fold it to a compile-time
                // `usize` `Inst::Const` (no `Inst::Call`, so the body stays interpretable and
                // flippable). Recognized HERE (before `resolve_callee`, which would reject the
                // intrinsic) — once recognized we own the outcome (`lower_offset_of` returns the const
                // or fails closed with its own precise tag), so return unconditionally.
                if let ty::FnDef(def_id, _) = self.thir.exprs[*fun].ty.kind() {
                    if self.tcx.lang_items().offset_of() == Some(*def_id) {
                        return self.lower_offset_of(expr_span, expr_ty, *fun, args);
                    }
                }
                // Trust: resolve the callee — direct free fn (unchanged), resolved
                // method/operator instance, or a fn-pointer value (indirect). Every
                // unresolvable shape fails closed with a precise split tag (see
                // `resolve_callee` for the tag taxonomy).
                let callee = match self.resolve_callee(*fun, *from_hir_call) {
                    Ok(k) => k,
                    Err(tag) => {
                        self.unsupported.push((format!("{expr_span:?}"), tag));
                        return None;
                    }
                };
                let arg_ids: Vec<ExprId> = args.iter().copied().collect();
                match callee {
                    CalleeKind::Direct(callee) => {
                        // Trust (realbody, opaque-lane Option READ): `<opaque Option lane>.is_some()`
                        // / `.is_none()` lowers as an opaque bool (opaque `call @callee` receiver =
                        // the `Ty::Unit` lane), NOT declining on the `&(*p).f` receiver borrow +
                        // non-scalar Option field. Fail-closed for any non-opaque receiver.
                        if let Some(v) = self.try_lower_opaque_option_read(*fun, &arg_ids, callee) {
                            return Some(v);
                        }
                        // Trust (wave-28): a `-> !` callee makes this call expr `ty::Never`
                        // (`expr_ty.is_never()`) — a diverging call whose effect-free const args may
                        // be dropped if unmappable (unblocks `assert_eq!`/`assert_ne!`).
                        // Trust (wave-MC): an explicit call/method (`from_hir_call`) admits the
                        // method-receiver-place-value fallback for its addressless `&mut (*p).f`
                        // receiver (see `try_lower_receiver_place_value`).
                        let arg_vals = self.lower_call_args(
                            expr_span,
                            &arg_ids,
                            expr_ty.is_never(),
                            *from_hir_call,
                            // Trust (wave-ER): a unit-returning callee is a candidate
                            // logging SINK for the read-only-plumbing arg drop.
                            expr_ty.is_unit(),
                        )?;
                        // Trust (merge): the parallel session's `emit_call` gives a unit-returning
                        // call ZERO results (the IR's unit convention); a non-unit call gets one.
                        // An opaque-lane Option is a non-unit rustc type, so the wave-SEAM ledger
                        // below layers cleanly onto the `Some(res)` it returns.
                        let res = self.emit_call(Inst::Call { callee, args: arg_vals }, expr_ty);
                        // Trust (wave-SEAM): ledger a LOCAL callee's opaque-lane-Option result
                        // as a PROVEN discriminant value (`option_lane_values`). A LOCAL fn's
                        // declaration carries `lower_fn`'s mapped signature, whose return for
                        // an opaque-lane Option is the flag's `Ty::Bool` (map_ty's enum arm) —
                        // the real seam producer `VecDeque::pop_front(&mut self) ->
                        // Option<Event>` (its body's `None` tail lowers via the value-lane
                        // ctor, so decl and body agree). An EXTERN/std callee's result is
                        // deliberately NOT ledgered: its decl is not ours (surrogate-typed),
                        // so the downstream value-lane test fails closed on it (keeping the
                        // pre-wave paths verbatim). CAVEAT (documented, fail-closed in
                        // effect): a local callee whose BODY later declines is emitted with a
                        // surrogate decl — its ledgered result would type-drift, but every
                        // consumer of the ledger forces `contains_call` (NotRun), so the
                        // drift is never interpreted; the honest fix is body-lowering, which
                        // the seam's stub guarantees for itself.
                        if option_flag_lanes_enabled()
                            && matches!(expr_ty.kind(), ty::Adt(a, _)
                                if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
                            && self.is_opaque_lane_enum(expr_ty)
                        {
                            let mut f = *fun;
                            loop {
                                match &self.thir.exprs[f].kind {
                                    ExprKind::Scope { value, .. } => f = *value,
                                    ExprKind::Use { source } => f = *source,
                                    _ => break,
                                }
                            }
                            if matches!(self.thir.exprs[f].ty.kind(),
                                ty::FnDef(did, _) if did.is_local())
                            {
                                // `res` is `Some` here: an opaque-lane Option is a non-unit rustc
                                // type, so `emit_call` above declared a result value.
                                if let Some(rv) = res {
                                    self.option_lane_values.push(rv);
                                }
                            }
                        }
                        res
                    }
                    // Trust: rust-call UNTUPLING — `Fn`/`FnMut::call{,_mut}` on a proven
                    // non-capturing local closure (`resolve_fn_trait_callee`). The THIR args
                    // are exactly `[receiver, (tupled-args)]`; the closure BODY's signed
                    // convention is `(env: Ptr, declared…)`, so emit
                    // `Inst::Call { callee, args: [env, untupled…] }` with:
                    //   * `env` — a fresh `Alloca` of the (empty, zero-sized) environment
                    //     (`Ty::Unit` pointee): with zero captures the body can contain no
                    //     upvar projection, so this pointer is indistinguishable from a
                    //     pointer to the real closure place within the fragment (pointer
                    //     comparisons/casts fail closed everywhere in it);
                    //   * the receiver DISCARDED only after being proven effect-free
                    //     (`effect_free_closure_receiver`) — otherwise dropping it would drop
                    //     observable effects: fail closed;
                    //   * the tuple operand split per `lower_closure_call_untupled` (element
                    //     order = MIR's tuple-temp field evaluation order).
                    CalleeKind::ClosureCall { callee, capturing } => {
                        // Defensive: the `Fn*::call*` THIR shape is exactly two args.
                        if arg_ids.len() != 2 {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Call(rust-call ABI)"));
                            return None;
                        }
                        // The env argument: for a CAPTURING closure (wave-CF) materialize the real
                        // env from the closure local; for a non-capturing closure (wave-5) discard
                        // the proven-effect-free receiver and pass a fresh unit-slot Ptr.
                        let env = if capturing {
                            match self.materialize_closure_env(expr_span, arg_ids[0]) {
                                Some(e) => e,
                                None => return None, // tag pushed inside
                            }
                        } else {
                            if !self.effect_free_closure_receiver(arg_ids[0]) {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Call(closure env unsupported)",
                                ));
                                return None;
                            }
                            let e = self.fresh();
                            self.push_node(InstrNode::new(Inst::Alloca {
                                    ty: Ty::Unit,
                                    count: None,
                                    align: None,
                                })
                                .with_result(e),
                            );
                            e
                        };
                        let untupled = self.lower_closure_call_untupled(expr_span, arg_ids[1])?;
                        let mut args = Vec::with_capacity(untupled.len() + 1);
                        args.push(env);
                        args.extend(untupled);
                        self.emit_call(Inst::Call { callee, args }, expr_ty)
                    }
                    // Trust: INDIRECT call through a fn-pointer value — `Inst::CallIndirect`
                    // with the callee's mapped `FuncTy` signature (the pended per-body id;
                    // see `map_fn_ptr_ty`). Evaluation order matches MIR: the callee operand
                    // is evaluated first, then the args left-to-right.
                    CalleeKind::FnPtr(fun_expr) => {
                        let fun_rty = self.thir.exprs[fun_expr].ty;
                        let mapped = self.map_ty(fun_rty);
                        let Ty::Func(sig) = mapped else {
                            // `map_ty` already recorded the precise "Ty(fn-ptr)" gap; this
                            // secondary tag marks the CALL as the consumer that needed it.
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Call(fn-ptr unsupported sig)"));
                            return None;
                        };
                        let callee_val = match self.lower_expr(fun_expr) {
                            Some(v) => v,
                            None => {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Call(fn-ptr callee unsupported)",
                                ));
                                return None;
                            }
                        };
                        // Defensive: a borrow-produced Ptr is never a fn-pointer value; a
                        // type-confused callee would make the CallIndirect ill-typed.
                        if self.is_borrow_ptr(callee_val) {
                            self.unsupported.push((
                                format!("{expr_span:?}"),
                                "Call(fn-ptr callee unsupported)",
                            ));
                            return None;
                        }
                        // Trust (wave-28): an indirect call to a `-> !` fn pointer is diverging too.
                        // An indirect (fn-pointer) call has no method-receiver borrow to recover.
                        let arg_vals = self.lower_call_args(
                            expr_span,
                            &arg_ids,
                            expr_ty.is_never(),
                            false,
                            false,
                        )?;
                        self.emit_call(
                            Inst::CallIndirect {
                                callee: callee_val,
                                sig,
                                args: arg_vals,
                                // The fragment admits only `extern "Rust"` fn-ptr sigs
                                // (`map_fn_ptr_ty` gates on the header ABI).
                                calling_conv: trust_ir::CallingConv::Rust,
                            },
                            expr_ty,
                        )
                    }
                }
            }
            ExprKind::Return { value } => {
                let values: Vec<ValueId> = match value {
                    Some(v) => {
                        let rv = self.lower_expr(*v);
                        // Fail-closed: a borrow pointer must not escape via the return value — EXCEPT
                        // a ref-PARAM ptr (wave-14), which outlives the call, so `return x;` /
                        // `return &*x;` faithfully yields the same param ptr (the return type is
                        // `Ty::Ptr`, table-free → splices). A `&local` snapshot ptr is not in
                        // `ref_param_ptrs`, so it stays fail-closed (and is borrowck-rejected anyway).
                        if let Some(rv) = rv {
                            // Trust (wave-16): a promoted-borrow GlobalAddr ptr (`global_ptrs`) is
                            // `'static`, so `return &5;` faithfully yields the global's address.
                            // Trust (wave-25b): a derived INTERIOR ptr (`interior_ptrs`) — `&self.field`
                            // off a ref param — addresses caller memory that outlives the call, so
                            // `return &self.field;` faithfully yields the same interior address.
                            if self.is_borrow_ptr(rv)
                                && !self.ref_param_ptrs.contains(&rv)
                                && !self.global_ptrs.contains(&rv)
                                && !self.interior_ptrs.contains(&rv)
                            {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Return(borrow ptr escapes)"));
                                return None;
                            }
                        }
                        rv.into_iter().collect()
                    }
                    None => Vec::new(),
                };
                // Unit-returning fns return no values (the bridge convention; see `lower_fn`) —
                // covers `return;` and `return unit_expr;` alike.
                let values = if self.fn_return_rty.is_some_and(|t| t.is_unit()) {
                    Vec::new()
                } else {
                    values
                };
                // The value walk may itself have sealed the block: a diverging value
                // (`return (return x)`) seals via its own terminator, and a value
                // `if`/`match` whose arms ALL sealed (each diverged or failed closed —
                // e.g. every arm an unsupported union literal) returns `None` with the
                // cursor sealed (`lower_if_value` step 7). Either way this `return` is
                // unreachable from the sealed block — sealing again would double-seal.
                // Mirrors the `!self.sealed` tail guard in `lower_fn`.
                if self.sealed {
                    return None;
                }
                self.seal_with(Inst::Return { values });
                None
            }
            // Trust: assignment to a local — `y = rhs`. SSA value-versioning: lower `rhs` to a fresh
            // ValueId and rebind the local to it (`set_local`, last-write-wins). This is the in-block
            // half of mutable-local support; the cross-block half (a local assigned inside an `if`/
            // `match` arm) is handled by the block-parameter merge in `lower_if`/`lower_match`, which
            // diff the per-arm `locals` snapshots against the pre-split snapshot to know which locals
            // need a join param. Fail-closed: a non-local LHS (field/index/deref place) is unsupported
            // — versioning it would need a memory model we do not have. `Assign` is unit-typed in
            // Rust, so it produces no value (return `None`), matching MIR (`a = b` is a statement).
            ExprKind::Assign { lhs, rhs } => {
                let lhs = *lhs;
                let rhs = *rhs;
                // Trust: WRITE THROUGH A `&mut` POINTER — `*r = v`. The lhs is an `ExprKind::Deref`
                // whose `arg` lowers to a `&mut`-produced slot Ptr (or, wave-5, a `&mut T`
                // scalar-pointee PARAM — the caller's slot Ptr, registered at binding); we `Store`
                // the rhs through it so a later `Load` of the same slot sees the new value.
                // FAIL-CLOSED if the deref target is not a known mutable borrow pointer (a `*p` write
                // through a raw pointer, a shared `&` (read-only — the mut ledger enforces Load-only
                // on shared refs, params included), or anything we did not register).
                if let Some(deref_arg) = self.deref_place_arg(lhs) {
                    let rhs_rty = self.thir.exprs[rhs].ty;
                    // Lower the pointer operand FIRST (it must be a mutable borrow ptr), then the rhs.
                    let ptr = match self.lower_expr(deref_arg) {
                        Some(p) => p,
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Assign(*r= ptr no value)"));
                            return None;
                        }
                    };
                    if !self.is_mut_borrow_ptr(ptr) {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Assign(*r= non-mut-borrow ptr)"));
                        return None;
                    }
                    let ty = self.map_ty(rhs_rty);
                    if !is_scalar_ty(&ty) {
                        self.unsupported.push((format!("{expr_span:?}"), "Assign(*r= non-scalar)"));
                        return None;
                    }
                    let v = match self.lower_expr(rhs) {
                        Some(v) => v,
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Assign(*r= rhs no value)"));
                            return None;
                        }
                    };
                    // The stored value must itself be a plain scalar (never another borrow ptr — that
                    // would alias-escape the slot).
                    if self.is_borrow_ptr(v) {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Assign(*r= stores a borrow ptr)"));
                        return None;
                    }
                    self.push_node(InstrNode::new(Inst::Store {
                        ty,
                        ptr,
                        value: v,
                        volatile: false,
                        align: None,
                    }));
                    return None;
                }
                // Trust (wave-23; wave-31 NESTED + field-opaque RECONCILED): `(*p).field = v` AND
                // `(*p).a.b.….field = v` — a scalar field STORE through a `&mut Struct` ptr (the
                // ref-escape memory model), generalized VALUE-LEVEL over a chain of nested FIELD
                // projections AND tolerating opaque (non-pure) sibling lanes at every level. Still
                // exactly ONE whole-struct `Load(*p)` … `Store(*p)` round trip; the nesting is pure
                // aggregate-value surgery between them. For `s.a.b = v` (chain len 2):
                //   %o  = Load(*p)                 ; whole root struct (opaque siblings = Unit lanes)
                //   %i  = ExtractField(%o, a)      ; current inner struct (the holder is a real lane)
                //   %i2 = InsertField(%i, b, v)    ; new inner struct (sole changed scalar lane)
                //   %o2 = InsertField(%o, a, %i2)  ; new root struct
                //   Store(*p, %o2)
                // A len-1 chain emits the EXACT wave-23 Load/InsertField/Store triple (same
                // instruction + fresh-id order), so the one-level shim flip coherence is untouched.
                // The whole-struct type is the DETERMINISTIC opaque build (`struct_ty_rmw_opaque`,
                // `written_field = None`): scalar/pure lanes real, LOCAL struct HOLDERS recursed,
                // std-container/enum/ref siblings opaque `Ty::Unit`. Each INTERMEDIATE chain link
                // must resolve (in that registered build) to a `Ty::Struct` holder — a Vec/Option/
                // enum link fails closed — and the LEAF field must be a genuine scalar. `mode=NotRun`
                // (the `Load` reads the ref param) / never flips (the shim fails closed on the
                // opaque-param `Load`/`Store` and any non-scalar SSA temp).
                if let Some((ptr_expr, deref_expr, chain)) = self.field_chain_deref_place(lhs) {
                    let pointee_rty = self.thir.exprs[deref_expr].ty;
                    let (adt, gargs) = match pointee_rty.kind() {
                        ty::Adt(adt, gargs) if adt.is_struct() => (*adt, *gargs),
                        _ => {
                            self.unsupported.push((
                                format!("{expr_span:?}"),
                                "Assign((*p).field non-struct pointee)",
                            ));
                            return None;
                        }
                    };
                    let struct_ty = match self.struct_ty_rmw_opaque(adt, gargs, None) {
                        Some(t) => t,
                        None => {
                            self.unsupported.push((
                                format!("{expr_span:?}"),
                                "Assign((*p).field non-struct pointee)",
                            ));
                            return None;
                        }
                    };
                    // Walk the REGISTERED field types down the chain. `agg_tys[i]` = the struct value
                    // type at depth i (agg_tys[0] = the root pointee). Every intermediate link must be
                    // a registered `Ty::Struct` holder; the leaf must be a scalar (the sole store
                    // lane). Reading types from the registration (not a fresh `map_ty`) keeps the
                    // ExtractField/InsertField `ty`s in exact lock-step with the whole-struct value.
                    let mut agg_tys: Vec<Ty> = vec![struct_ty.clone()];
                    // Trust (realbody): set when the leaf lane is an OPAQUE `Ty::Unit` placeholder,
                    // routing codegen to an opaque insertfield instead of a real scalar store.
                    let mut leaf_opaque = false;
                    // Trust (wave-ER): set (to the lane's REGISTERED type) when the leaf is a REAL
                    // non-Unit NON-SCALAR lane being replaced WHOLE — `self.storage.rows = new_rows;
                    // self.storage.pages = new_pages;` (the erase ring-rebuild installs). The store
                    // commits `undef <lane ty>` — "an unknown value of the lane's registered type" —
                    // see the newleaf arm below for the soundness argument.
                    let mut leaf_container: Option<Ty> = None;
                    // Trust (wave-OPTFLAG): the leaf's REGISTERED scalar type (captured when the
                    // chain walk reaches a genuine scalar lane), used to recognize an
                    // Option-DISCRIMINANT `Ty::Bool` lane under `TRUST_OPTION_FLAG_LANES=1`.
                    let mut leaf_reg_ty: Option<Ty> = None;
                    for k in 0..chain.len() {
                        let Ty::Struct(sid) = agg_tys[k] else {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Assign(nested non-struct link)"));
                            return None;
                        };
                        let fts = match self.registered_struct_field_tys(sid) {
                            Some(v) => v,
                            None => {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign(nested unregistered link)",
                                ));
                                return None;
                            }
                        };
                        let field_ty = match fts.get(chain[k].1 as usize) {
                            Some(t) => t.clone(),
                            None => {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign(nested field index oob)",
                                ));
                                return None;
                            }
                        };
                        if k + 1 < chain.len() {
                            if !matches!(field_ty, Ty::Struct(_)) {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign(nested non-struct link)",
                                ));
                                return None;
                            }
                            agg_tys.push(field_ty);
                        } else if !is_scalar_ty(&field_ty) {
                            // Trust (realbody): a non-scalar leaf that `struct_ty_rmw_opaque` collapsed
                            // to an OPAQUE `Ty::Unit` lane (a Vec/Option/data-enum sibling — the real
                            // `GridStorage.damage: Damage` / `.scrollback: Option<_>` shape) is a store
                            // into an UNPROJECTED opaque field: lower it as an opaque insertfield (below)
                            // rather than decline.
                            //
                            // Trust (wave-ER): a REAL registered non-scalar lane (`Ty::Struct`/
                            // `Ty::Tuple` — the erase whole-container installs `rows = new_rows` /
                            // `pages = new_pages`) is a WHOLE-VALUE replacement write: admitted, with
                            // the stored value degraded to `undef <lane ty>` (see the newleaf arm).
                            // A projected lane can never be such a lane BY CONSTRUCTION: every
                            // projection kind (bool / counter / change-latch / option_flag) lives on
                            // a SCALAR registered lane, and a scalar lane takes the scalar arm above —
                            // so this arm only ever writes lanes the temporal model does not track
                            // (and the extractor additionally hard-errors if an opaque value is ever
                            // committed to a projected place — its own fail-closed tooth).
                            if matches!(field_ty, Ty::Unit) {
                                leaf_opaque = true;
                            } else {
                                leaf_container = Some(field_ty);
                            }
                        } else {
                            leaf_reg_ty = Some(field_ty);
                        }
                    }
                    // Pointer first (a `&mut Struct` slot ptr), then the rhs — same order as `*r=v`.
                    // Trust (wave-DP): an AUTO-DEREF-MUT CHAIN pointer (`self.storage.damage = …`
                    // through the GridStorage→GridCursorState DerefMut hops) lowers FIRST as the
                    // structure-carrying opaque call chain (`lower_deref_mut_chain_ptr`); every
                    // other ptr shape takes the pre-wave path (and its tags) unchanged.
                    let ptr = match self.lower_deref_mut_chain_ptr(ptr_expr) {
                        Some(p) => p,
                        None => match self.lower_expr(ptr_expr) {
                            Some(p) => p,
                            None => {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign((*p).field ptr no value)",
                                ));
                                return None;
                            }
                        },
                    };
                    if !self.is_mut_borrow_ptr(ptr) {
                        self.unsupported.push((
                            format!("{expr_span:?}"),
                            "Assign((*p).field non-mut-borrow ptr)",
                        ));
                        return None;
                    }
                    // Trust (wave-OPTFLAG): an Option-DISCRIMINANT `Ty::Bool` lane — the leaf's
                    // RUSTC type is the Option lang enum with a NON-pure-value payload, exactly
                    // the lane `struct_ty_rmw_opaque` registers `Ty::Bool` under
                    // `TRUST_OPTION_FLAG_LANES=1` (a genuine `bool` field has a `bool` rustc
                    // leaf type and never enters this arm). A LITERAL `Some(..)` / `None`
                    // constructor RHS has a STATIC discriminant and lowers as `const bool`;
                    // the PAYLOAD expression is deliberately NOT lowered (identical to the
                    // pre-wave opaque arm, which dropped the whole ctor RHS — CLEAN-ONLY
                    // `NotRun` bodies). Any other RHS — a copied/computed Option VALUE, whose
                    // discriminant is unknown at this abstraction — commits `undef bool`
                    // (wave-RS: the wave-ER whole-container-replacement posture; pre-wave it
                    // failed closed, which REGRESSED four real setter bodies flag-ON, e.g.
                    // `self.complex_char = s.map(Box::new);` — measured 2026-07-13). The undef
                    // is a sound HAVOC of the discriminant: a projected optflag lane written
                    // this way fails closed downstream at the extractor's write abstraction
                    // (an opaque commit to a projected place), never a fabricated bit.
                    // `Some(Some(d))` = static disc, `Some(None)` = unknown disc (undef),
                    // `None` = not an optflag lane.
                    let option_flag_disc: Option<Option<bool>> = if option_flag_lanes_enabled()
                        && matches!(leaf_reg_ty, Some(Ty::Bool))
                        && {
                            // A `Ty::Bool` REGISTERED lane under an `Option`-typed rustc leaf can
                            // ONLY be the wave's discriminant lane (a genuine `bool` field has a
                            // `bool` rustc leaf; a cleanly-mapped pure `Option<scalar>` keeps its
                            // real `{tag, payload}` struct lane and never registers `Ty::Bool`) —
                            // the exact mirror of the `struct_ty_rmw_opaque` registration arm.
                            let leaf_rty = self.thir.exprs[chain[chain.len() - 1].0].ty;
                            matches!(leaf_rty.kind(), ty::Adt(a, _)
                                if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
                        } {
                        // Peel Scope/Use to the ctor; snapshot Copy data BEFORE any `&mut self`
                        // call (the `self.thir` borrow must drop first — the ExprKind::Adt idiom).
                        let mut r = rhs;
                        loop {
                            match &self.thir.exprs[r].kind {
                                ExprKind::Scope { value, .. } => r = *value,
                                ExprKind::Use { source } => r = *source,
                                _ => break,
                            }
                        }
                        let ctor: Option<(DefId, bool)> = match &self.thir.exprs[r].kind {
                            ExprKind::Adt(adt_expr) if adt_expr.adt_def.is_enum() => Some((
                                adt_expr.adt_def.variant(adt_expr.variant_index).def_id,
                                matches!(adt_expr.base, rustc_middle::thir::AdtExprBase::None),
                            )),
                            _ => None,
                        };
                        let li = self.tcx.lang_items();
                        match ctor {
                            Some((vdid, true)) if li.option_some_variant() == Some(vdid) => {
                                Some(Some(true))
                            }
                            Some((vdid, true)) if li.option_none_variant() == Some(vdid) => {
                                Some(Some(false))
                            }
                            // Copied/computed Option value: unknown discriminant → undef.
                            _ => Some(None),
                        }
                    } else {
                        None
                    };
                    // Scalar leaf: lower the real RHS and store it. Opaque `Ty::Unit` leaf: do NOT
                    // lower the enum/Option constructor RHS — an opaque value is stored below.
                    let v_scalar = if leaf_opaque {
                        None
                    } else if leaf_container.is_some() {
                        // Trust (wave-ER, whole-container replacement): the RHS is still LOWERED —
                        // its evaluation may carry effects (a ctor call) and an unloweable RHS must
                        // keep failing closed (never a silently-dropped effect) — but its VALUE is
                        // deliberately DISCARDED: the store below commits `undef <lane ty>` instead.
                        // No borrow-ptr escape check is needed: the value never enters the aggregate.
                        if self.lower_expr(rhs).is_none() {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Assign(container rhs no value)"));
                            return None;
                        }
                        None
                    } else if let Some(disc) = option_flag_disc {
                        let c = self.fresh();
                        match disc {
                            // Trust (wave-OPTFLAG): the static discriminant IS the stored scalar.
                            Some(d) => {
                                self.push_node(InstrNode::new(Inst::Const {
                                        ty: Ty::Bool,
                                        value: Constant::Bool(d),
                                    })
                                    .with_result(c),
                                );
                            }
                            // Trust (wave-RS): unknown discriminant — HAVOC the lane with
                            // `undef bool`. `contains_call` is FORCED (the wave-ER container
                            // arm's posture): an eager-UB `undef` must never be interpreted,
                            // so the body stays structurally NotRun (CLEAN-ONLY). The RHS is
                            // deliberately not lowered — the same drop the literal-ctor arm
                            // (and the pre-wave opaque arm) applies to the payload expr.
                            None => {
                                self.contains_call = true;
                                self.push_node(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(c),
                                );
                            }
                        }
                        Some(c)
                    } else {
                        let v = match self.lower_expr(rhs) {
                            Some(v) => v,
                            None => {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign((*p).field rhs no value)",
                                ));
                                return None;
                            }
                        };
                        // The stored scalar must not itself be a borrow ptr (that would alias-escape a
                        // pointer into the struct) — same guard as the `*r=v` arm.
                        if self.is_borrow_ptr(v) {
                            self.unsupported.push((
                                format!("{expr_span:?}"),
                                "Assign((*p).field stores a borrow ptr)",
                            ));
                            return None;
                        }
                        Some(v)
                    };
                    // Load the root, then extract DOWN the chain to the leaf's parent aggregate.
                    // `aggs[i]` = the pre-state aggregate VALUE at depth i (aggs[0] = the root).
                    let root = self.fresh();
                    self.push_node(InstrNode::new(Inst::Load {
                            ty: struct_ty.clone(),
                            ptr,
                            volatile: false,
                            align: None,
                        })
                        .with_result(root),
                    );
                    let mut aggs: Vec<ValueId> = vec![root];
                    for i in 0..chain.len() - 1 {
                        let sub = self.fresh();
                        self.push_node(InstrNode::new(Inst::ExtractField {
                                // Result-typed, matching the `Field` read arm's convention.
                                ty: agg_tys[i + 1].clone(),
                                aggregate: aggs[i],
                                field: chain[i].1,
                            })
                            .with_result(sub),
                        );
                        aggs.push(sub);
                    }
                    // The new leaf value: the lowered scalar, or (opaque lane) the leaf's OWN loaded
                    // `Ty::Unit` value re-extracted and re-inserted — `Ty::Unit` is single-valued, so
                    // this is EXACT for the unprojected lane (never observed; round-trips untouched).
                    //
                    // Trust (wave-ER, whole-container replacement): a REAL non-scalar lane replaced
                    // whole commits `undef <lane ty>` — the honest "an UNKNOWN value of the lane's
                    // registered type" (the ring-rebuild's `new_rows`/`new_pages` carry no
                    // interpretable content: they were built by opaque calls / a summarized loop).
                    // SOUNDNESS: (a) the lane is UNPROJECTED by construction (projection kinds are
                    // scalar-lane-only — see the admission comment above), so the model never reads
                    // it; the extractor sees an opaque value committed to an unprojected place (a
                    // no-op for the derived command) and HARD-ERRORS if its projection table ever
                    // maps a projected var here; (b) `Inst::Undef` is eager-UB under the reference
                    // interpreter, so `contains_call` is FORCED — the body is structurally NotRun,
                    // never interpreted, and the flip differential fails closed on the out-of-
                    // fragment `Undef` (DerivedUnsupported) — CLEAN-ONLY, exactly the wave-28
                    // posture.
                    let newleaf = match v_scalar {
                        Some(v) => v,
                        None => {
                            if let Some(cty) = leaf_container.clone() {
                                self.contains_call = true;
                                let leaf = self.fresh();
                                self.push_node(InstrNode::new(Inst::Undef { ty: cty }).with_result(leaf),
                                );
                                leaf
                            } else {
                                let leaf = self.fresh();
                                self.push_node(InstrNode::new(Inst::ExtractField {
                                        ty: Ty::Unit,
                                        aggregate: aggs[chain.len() - 1],
                                        field: chain[chain.len() - 1].1,
                                    })
                                    .with_result(leaf),
                                );
                                leaf
                            }
                        }
                    };
                    // Insert the new leaf into its parent, then re-insert each rebuilt aggregate
                    // back UP the chain (siblings at every level round-trip unchanged).
                    let mut newval = newleaf;
                    for i in (0..chain.len()).rev() {
                        let next = self.fresh();
                        self.push_node(InstrNode::new(Inst::InsertField {
                                ty: agg_tys[i].clone(),
                                aggregate: aggs[i],
                                field: chain[i].1,
                                value: newval,
                            })
                            .with_result(next),
                        );
                        newval = next;
                    }
                    self.push_node(InstrNode::new(Inst::Store {
                        ty: struct_ty,
                        ptr,
                        value: newval,
                        volatile: false,
                        align: None,
                    }));
                    return None;
                }
                let var = match self.place_local(lhs) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Assign(non-local place)"));
                        return None;
                    }
                };
                let rhs_rty = self.thir.exprs[rhs].ty;
                match self.lower_expr(rhs) {
                    Some(v) => {
                        let ty = self.map_ty(rhs_rty);
                        // Trust: a PROMOTED local is memory-backed — a direct `local = v` is a `Store`
                        // to its slot (NOT an SSA rebind), so a later `Load` reads the new value and a
                        // `&mut local` alias still observes it.
                        if self.is_promoted(var) {
                            let slot = match self.promoted_slot(var) {
                                Some(s) => s,
                                None => {
                                    self.unsupported.push((
                                        format!("{expr_span:?}"),
                                        "Assign(promoted slot missing)",
                                    ));
                                    return None;
                                }
                            };
                            if self.is_borrow_ptr(v) {
                                self.unsupported.push((
                                    format!("{expr_span:?}"),
                                    "Assign(promoted stores a borrow ptr)",
                                ));
                                return None;
                            }
                            self.push_node(InstrNode::new(Inst::Store {
                                ty,
                                ptr: slot,
                                value: v,
                                volatile: false,
                                align: None,
                            }));
                        } else {
                            self.set_local(var, v, ty);
                        }
                        None
                    }
                    None => {
                        // RHS was unsupported (its own `unsupported` recorded) or diverged. Either
                        // way we cannot rebind the local; the gate is already red.
                        self.unsupported.push((format!("{expr_span:?}"), "Assign(rhs no value)"));
                        None
                    }
                }
            }
            // Trust: compound assignment `x += e` / `x /= e` / … (the *non-overloaded*
            // `ExprKind::AssignOp`; an overloaded `+=` on a user type desugars to a method call and
            // never reaches here). Lowered as the MIR-faithful read-binop-write — see
            // `lower_assign_op` for the exact operand order and place forms.
            ExprKind::AssignOp { op, lhs, rhs } => {
                let op = *op;
                let lhs = *lhs;
                let rhs = *rhs;
                self.lower_assign_op(expr_span, op, lhs, rhs)
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                let cond = *cond;
                let then = *then;
                let else_opt = *else_opt;
                self.lower_if(expr_ty, expr_span, cond, then, else_opt)
            }
            ExprKind::LogicalOp { op, lhs, rhs } => {
                let op = *op;
                let lhs = *lhs;
                let rhs = *rhs;
                self.lower_logical_op(expr_span, op, lhs, rhs)
            }
            // Trust (wave-ER, let-chain / if-let over an OPAQUE enum value): the `let PAT = scrut`
            // CONDITION expression (THIR `ExprKind::Let` — `if let …`, `… && let …` chains). See
            // `lower_let_opaque_test` for the admission gates and the soundness argument.
            ExprKind::Let { expr, pat } => {
                let scrut = *expr;
                // Extract the pattern's admissibility + by-value binding vars in a read-only
                // pass (the `&self.thir` borrow must end before the `&mut self` lowering calls).
                let binds = self.let_pat_bindings(pat);
                // Trust (wave-SEAM): the tested Option variant, for the value-lane arm.
                let variant_test = Self::option_pat_variant_test(pat);
                self.lower_let_opaque_test(expr_span, scrut, binds, variant_test)
            }
            ExprKind::Match { scrutinee, arms, match_source } => {
                let scrutinee = *scrutinee;
                let arm_ids: Vec<rustc_middle::thir::ArmId> = arms.iter().copied().collect();
                // Trust: the `?`-operator desugars (in HIR) to
                //   match Try::branch(x) { Continue(v) => v, Break(r) => return from_residual(r) }
                // carrying `MatchSource::TryDesugar`. `Try::branch`/`from_residual` are TRAIT METHODS
                // the producer cannot resolve to a concrete `FuncId`, and `ControlFlow<Residual,_>` is a
                // heterogeneous/non-scalar enum the `(tag,payload)` model cannot represent — so the
                // generic match arms fail closed. Instead we recognize the desugar and lower it
                // SEMANTICALLY from the original operand `x` (a concrete `Result<T,E>`/`Option<T>`):
                //   x?  ≡  match x { Ok(v)/Some(v) => v, Err(e) => return Err(e) / None => return None }
                // for the IDENTITY case (the operand's error/None type matches the fn return). See
                // `lower_try_question`.
                if matches!(match_source, rustc_hir::MatchSource::TryDesugar(_)) {
                    return self.lower_try_question(expr_ty, expr_span, scrutinee);
                }
                // Trust (wave-ER): the `for` desugar (`match into_iter(it) { mut iter =>
                // loop { match iter.next() { … } } }`, `MatchSource::ForLoopDesugar`) has
                // ALWAYS declined (the `mut iter` whole-value binding is rejected by the
                // tuple-match classifier), so trying the READ-ONLY-ESCAPE LOOP SUMMARY first
                // can only change previously-declined bodies. If the summary's structural
                // gate refuses (any non-local write / mut-borrow, any control-flow escape),
                // fall through to the normal path — and its pre-existing decline — unchanged.
                if matches!(match_source, rustc_hir::MatchSource::ForLoopDesugar) {
                    if self.try_lower_foreach_summary(expr_ty, expr_span, scrutinee, &arm_ids) {
                        return None; // unit-typed `for` — summarized, no value.
                    }
                    // Trust (wave-DR): the summary refused (the region has a write channel
                    // the local gate cannot see — e.g. the drain transfer loop's
                    // `scrollback.push_line(line)` through the opaque-carrier payload).
                    // Lower the desugar VISIBLY instead: a real back-edge CFG whose body
                    // carries the per-iteration `next(iter)` pop and the loop body's own
                    // lowered effects — the data flow the temporal extractor must SEE
                    // (never summarize-by-erasure; see `lower_for_desugar_outer`).
                    return self.lower_for_desugar(expr_ty, expr_span, scrutinee, &arm_ids);
                }
                self.lower_match(expr_ty, expr_span, scrutinee, arm_ids)
            }
            // Trust: tuple construction `(a, b, …)` → a runtime trust-ir aggregate.
            //
            // We CANNOT seed the aggregate with `Inst::Undef` + `InsertField`: the reference
            // interpreter executes `Undef` as EAGER `UndefinedBehavior` (trust-ir interpret.rs ~502),
            // which would make every tuple-constructing body non-interpretable (the oracle-blindness
            // cause). Instead we seed with a fully-typed `Inst::Const { Ty::Tuple, Constant::Aggregate }`
            // whose element placeholders carry the right field types, then `InsertField` each lowered
            // runtime field value over it. `eval_insert_field` only requires the seed already be an
            // `Aggregate` of the matching field types — which the typed `Const` seed satisfies — so the
            // result is a genuine runtime aggregate carrying the field VALUES, fully interpretable.
            ExprKind::Tuple { fields } => {
                let field_ids: Vec<ExprId> = fields.iter().copied().collect();
                // The empty tuple `()` is unit — no value on the existing 0-value path.
                if field_ids.is_empty() {
                    return None;
                }
                let tuple_ty = self.map_ty(expr_ty);
                // map_ty guarantees a non-empty tuple maps to `Ty::Tuple`; bail fail-closed otherwise
                // (e.g. an element type was unsupported and the whole thing degraded).
                let Ty::Tuple(field_tys) = tuple_ty.clone() else {
                    self.unsupported.push((format!("{expr_span:?}"), "Tuple(non-tuple mapped ty)"));
                    return None;
                };
                if field_tys.len() != field_ids.len() {
                    self.unsupported.push((format!("{expr_span:?}"), "Tuple(arity mismatch)"));
                    return None;
                }
                // Lower each field FIRST (fail-closed if any is unsupported — never an aggregate hole).
                // Trust (wave-UF): a `()` unit element is value-less (`Option::None` slot); its
                // `Constant::PhantomData` seed lane is the final value.
                let mut field_vals: Vec<Option<ValueId>> = Vec::with_capacity(field_ids.len());
                for (_i, f) in field_ids.iter().enumerate() {
                    // Gate on the element's REAL rust type (`ty::Tuple([])`), NOT the mapped `Ty::Unit`
                    // (also emitted as a degraded placeholder for an unsupported element — wave-UV/A4).
                    let f_is_unit =
                        matches!(self.thir.exprs[*f].ty.kind(), ty::Tuple(ts) if ts.is_empty());
                    let mark = self.unsupported.len();
                    match self.lower_expr(*f) {
                        Some(v) => {
                            // Fail-closed: a borrow pointer must not escape into a tuple field.
                            if self.is_borrow_ptr(v) {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Tuple(borrow ptr field)"));
                                return None;
                            }
                            field_vals.push(Some(v))
                        }
                        None => {
                            // Trust (wave-UF): a `()` unit element produces no runtime value. Its side
                            // effects (if any) were already lowered; if lowering pushed no gap tag, did
                            // NOT seal the block, AND the element is a real unit, keep it value-less
                            // (its PhantomData seed slot is the final zero-size value — a single
                            // inhabitant, so flip-faithful by construction). The `!self.sealed` guard is
                            // load-bearing: a DIVERGING `()`-typed element (`(1, return 7)` — `!` coerces
                            // to `()` via `NeverToAny`) seals the block; accepting it would emit the seed
                            // into a sealed cursor (malformed IR). Any real gap (a tag was pushed), a
                            // sealed block (diverged), or a non-unit `None` fails closed.
                            if self.unsupported.len() == mark && !self.sealed && f_is_unit {
                                field_vals.push(None);
                            } else {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Tuple(unsupported field)"));
                                return None;
                            }
                        }
                    }
                }
                // Typed seed: a `Ty::Tuple` constant whose elements are interpretable placeholder
                // constants of each field type (Int(0) for ints, Bool(false) for bools). This is the
                // NON-Undef fresh-aggregate seed the interpreter handles eagerly. Trust (wave-13):
                // `seed_constant_ty` recurses over nested `Ty::Struct`/`Ty::Tuple` elements (was
                // scalar-only), so a tuple-of-struct like `(Inner{..}, i32)` seeds a well-typed nested
                // `Constant::Aggregate` instead of falling closed; a non-seedable leaf still declines
                // the whole tuple. Every seed lane is overwritten by an `InsertField` below.
                let seed_consts: Vec<Constant> = match field_tys
                    .iter()
                    .map(|t| self.seed_constant_ty(t, 0))
                    .collect::<Option<Vec<_>>>()
                {
                    Some(c) => c,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Tuple(non-scalar field seed)"));
                        return None;
                    }
                };
                let mut agg = self.fresh();
                self.push_node(InstrNode::new(Inst::Const {
                        ty: tuple_ty.clone(),
                        value: Constant::Aggregate(seed_consts),
                    })
                    .with_result(agg),
                );
                // Insert each runtime field value over the seed, threading the aggregate ValueId.
                for (i, val) in field_vals.iter().enumerate() {
                    // Trust (wave-UF): skip a value-less unit element — its PhantomData seed is final.
                    let Some(val) = val else { continue };
                    let next = self.fresh();
                    self.push_node(InstrNode::new(Inst::InsertField {
                            ty: tuple_ty.clone(),
                            aggregate: agg,
                            field: i as u32,
                            value: *val,
                        })
                        .with_result(next),
                    );
                    agg = next;
                }
                Some(agg)
            }
            // Trust: struct construction `P { x: a, y: b }` → a runtime trust-ir aggregate, built with
            // the SAME machinery as tuples (a typed `Const`-seeded aggregate + `InsertField` per
            // field) under the FIRST-CLASS struct type `Ty::Struct(id)` — the pinned interpreter
            // materializes `(Ty::Struct, Constant::Aggregate)` seeds by resolving the module's
            // `StructDef` (foundations 93e8f16; scratch-verified incl. zero-field unit structs,
            // cmtest w4_struct (1)/(2)), and `InsertField`/`ExtractField` operate on the in-register
            // `Aggregate` value identically to tuples. This matches the MIR-side oracle's
            // `Struct(StructId)` signing, killing the 'THIR Tuple([..]) vs MIR Struct(StructId(N))'
            // signature-divergence class.
            //
            // FAIL-CLOSED: enums/unions (multi-variant / `!is_struct`), functional-record-update
            // (`..base`) and default-field (`..`) bases, an unregistered struct id (impossible for a
            // fresh `map_ty` result — checked anyway), or any field whose value/type is unsupported
            // → recorded `unsupported`, no partial aggregate emitted.
            ExprKind::Adt(adt_expr) => {
                // Snapshot all Copy data from the THIR `AdtExpr` BEFORE any `&mut self` call (the
                // borrow of `self.thir` via `expr` must be dropped first — mirrors `ExprKind::Tuple`).
                // `AdtDef` is Copy, so `adt` does not hold the `self.thir` borrow.
                let adt = adt_expr.adt_def;
                let _adt_args = adt_expr.args;
                let variant_index = adt_expr.variant_index;
                let base_is_none = matches!(adt_expr.base, rustc_middle::thir::AdtExprBase::None);
                // Trust (wave-FRU): the FRU base expr of `S { f: v, ..base }` (Copy `ExprId`), snapshot
                // BEFORE any `&mut self` call (the `self.thir` borrow via `adt_expr` must drop first).
                // `DefaultFields` (`Foo { .. }`) carries no base and stays `None` here → fail-closed.
                let fru_base: Option<ExprId> = match &adt_expr.base {
                    rustc_middle::thir::AdtExprBase::Base(fru) => Some(fru.base),
                    _ => None,
                };
                // Each field value goes at its DESTINATION index (`FieldExpr.name`), which is NOT
                // necessarily the source-write order. Collect `(index, ExprId)` (both Copy).
                let field_exprs: Vec<(usize, ExprId)> =
                    adt_expr.fields.iter().map(|f| (f.name.as_usize(), f.expr)).collect();
                // Trust (B3-2c T2): enum construction is GENERAL-ONLY — the legacy
                // (tag, payload) tuple ctor is deleted. lower_enum_construct_general
                // itself fails closed on unregistered enums (the opaque floor), so
                // spelling-follows-type holds by construction.
                if adt.is_enum() {
                    if !base_is_none {
                        self.unsupported.push((format!("{expr_span:?}"), "Adt(enum base/..)"));
                        return None;
                    }
                    return self.lower_enum_construct_general(
                        expr_span,
                        expr_ty,
                        variant_index,
                        &field_exprs,
                    );
                }
                // Struct only: a single (non-enum) variant. Unions are out of scope.
                if !adt.is_struct() {
                    self.unsupported.push((format!("{expr_span:?}"), "Adt(union)"));
                    return None;
                }
                // Trust (wave-FRU): a `..base` functional-record-update (`FruInfo::Base`) IS modeled —
                // the omitted fields are read from the lowered `base` value via `ExtractField` below.
                // Only `DefaultFields` (`Foo { .. }`, no base — omitted fields would come from const
                // defaults we don't thread) still fails closed.
                if !base_is_none && fru_base.is_none() {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Adt(struct default-fields ..)"));
                    return None;
                }
                // The mapped type is `Ty::Struct(id)` (registering the `StructDef`); its field
                // types come from the registered def (declaration order — the same order the
                // seed/`InsertField` indices use). Bail fail-closed if the mapping degraded
                // (e.g. an unsupported field type → `Ty::Unit` placeholder).
                let agg_ty = self.map_ty(expr_ty);
                let Ty::Struct(sid) = &agg_ty else {
                    self.unsupported.push((format!("{expr_span:?}"), "Adt(non-struct mapped ty)"));
                    return None;
                };
                let Some(field_tys) = self.registered_struct_field_tys(*sid) else {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Adt(unregistered struct id)"));
                    return None;
                };
                // Trust (wave-FRU): FRU gives a SUBSET of fields (the rest come from `base`); keep the
                // exact-count invariant only for plain (no-base) structs so their IR is byte-identical.
                // A too-many-fields count is always malformed.
                if (fru_base.is_none() && field_exprs.len() != field_tys.len())
                    || field_exprs.len() > field_tys.len()
                {
                    self.unsupported.push((format!("{expr_span:?}"), "Adt(field-count mismatch)"));
                    return None;
                }
                // Lower each field value FIRST (fail-closed if any is unsupported — never a hole),
                // recording it against its destination index.
                let mut field_vals: Vec<Option<ValueId>> = vec![None; field_tys.len()];
                // Trust (wave-UF): tracks slots accepted as a value-less real `()` field. Gated on the
                // field's RUST type, NOT the mapped `Ty::Unit` (which `map_ty` also emits as a
                // fail-closed placeholder for an unsupported field type — the wave-UV/wave-A4 lesson).
                // A `unit_field[i]` slot gets a `Constant::PhantomData` seed and NO `InsertField`; the
                // FRU + missing-field checks below treat it as legitimately value-less.
                let mut unit_field: Vec<bool> = vec![false; field_tys.len()];
                for (idx, fexpr) in field_exprs {
                    if idx >= field_tys.len() {
                        self.unsupported.push((format!("{expr_span:?}"), "Adt(field index OOB)"));
                        return None;
                    }
                    // The field value's real type IS the field's declared type; a genuine `()` field is
                    // `ty::Tuple([])` (the sole thing `map_ty` sends to `Ty::Unit` as a REAL unit,
                    // line ~824). This ground-truth test never mistakes a degraded `Ty::Unit`
                    // placeholder for a real unit.
                    let f_is_unit =
                        matches!(self.thir.exprs[fexpr].ty.kind(), ty::Tuple(ts) if ts.is_empty());
                    let mark = self.unsupported.len();
                    match self.lower_expr(fexpr) {
                        Some(v) => {
                            // Fail-closed: a borrow pointer must not escape into a struct field.
                            if self.is_borrow_ptr(v) {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Adt(borrow ptr field)"));
                                return None;
                            }
                            field_vals[idx] = Some(v)
                        }
                        None => {
                            // Trust (wave-UF): a `()` unit FIELD produces no runtime value (the
                            // producer models `()` as value-less). Its side effects (if any) were
                            // already lowered into `self.cur`; if lowering pushed no gap tag, did NOT
                            // seal the block, AND the field is a real unit, keep it value-less — its
                            // `Constant::PhantomData` seed slot (below) is the final zero-size value and
                            // gets no `InsertField`. The `!self.sealed` guard is load-bearing: a
                            // DIVERGING `()`-typed field value (`S { u: return 7 }` — `!` coerces to
                            // `()` via `NeverToAny`, so `f_is_unit` is true and no tag is pushed) seals
                            // the block; accepting it as a benign unit would emit the seed into a sealed
                            // cursor and return `Some(agg)`, breaking the `sealed ⇒ None` invariant
                            // (malformed IR). Any real gap (a tag was pushed), a sealed block (diverged),
                            // or a non-unit `None` still fails closed.
                            if self.unsupported.len() == mark && !self.sealed && f_is_unit {
                                unit_field[idx] = true; // field_vals[idx] stays None
                            } else {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Adt(unsupported field)"));
                                return None;
                            }
                        }
                    }
                }
                // Trust (wave-FRU): read each OMITTED field from the lowered `base` struct value via
                // `ExtractField{base, i}` — declaration-order field `i` is exactly the seed/InsertField
                // index (and `FruInfo`'s field order). The base is lowered AFTER the explicit fields
                // (Rust evaluates the fields, then the base). It must be a plain in-register struct
                // aggregate (not a borrow ptr) and every omitted field a scalar the `ExprKind::Field`
                // arm's `ExtractField` already proves readable; anything else fails closed. This is
                // additive: a `..base` body carried the `Adt(struct base/..)` tag before this wave, so
                // no previously-clean body reaches here (became_dirty == 0).
                if let Some(base_expr) = fru_base {
                    let base_val = match self.lower_expr(base_expr) {
                        Some(v) => v,
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Adt(unsupported FRU base)"));
                            return None;
                        }
                    };
                    if self.is_borrow_ptr(base_val) {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Adt(FRU base is borrow ptr)"));
                        return None;
                    }
                    for i in 0..field_tys.len() {
                        // Trust (wave-UF): skip a slot already provided OR accepted as a value-less real
                        // `()` field (its `Constant::PhantomData` seed is the final value — never filled
                        // from base). A degraded `Ty::Unit` placeholder is NOT in `unit_field`, so it
                        // still hits the non-scalar check below and fails closed.
                        if field_vals[i].is_some() || unit_field[i] {
                            continue;
                        }
                        let fty = field_tys[i].clone();
                        if !(is_scalar_ty(&fty) || matches!(fty, Ty::F32 | Ty::F64)) {
                            self.unsupported.push((
                                format!("{expr_span:?}"),
                                "Adt(FRU non-scalar omitted field)",
                            ));
                            return None;
                        }
                        let res = self.fresh();
                        self.push_node(InstrNode::new(Inst::ExtractField {
                                ty: fty,
                                aggregate: base_val,
                                field: i as u32,
                            })
                            .with_result(res),
                        );
                        field_vals[i] = Some(res);
                    }
                }
                // Every NON-unit field must now have been provided (explicit or filled from `base`).
                // Trust (wave-UF): a real `()` field (tracked in `unit_field`) is legitimately
                // value-less (its seed slot is the final value); only a missing NON-unit field is
                // malformed.
                for i in 0..field_tys.len() {
                    if field_vals[i].is_none() && !unit_field[i] {
                        self.unsupported.push((format!("{expr_span:?}"), "Adt(missing field)"));
                        return None;
                    }
                }
                // Typed aggregate seed (interpretable placeholders), then `InsertField` each runtime
                // field value over it in field-index order — identical to the tuple path. Trust
                // (wave-12): `seed_constant_ty` recurses over nested `Ty::Struct`/`Ty::Tuple` fields
                // (was scalar-only), so struct-of-struct construction seeds a well-typed nested
                // `Constant::Aggregate` instead of falling closed; a non-seedable leaf still declines
                // the whole construction. Every seed lane is overwritten by an `InsertField` below,
                // so the placeholder values are never observed.
                let seed_consts: Vec<Constant> = match field_tys
                    .iter()
                    .map(|t| self.seed_constant_ty(t, 0))
                    .collect::<Option<Vec<_>>>()
                {
                    Some(c) => c,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Adt(non-scalar field seed)"));
                        return None;
                    }
                };
                let mut agg = self.fresh();
                self.push_node(InstrNode::new(Inst::Const {
                        ty: agg_ty.clone(),
                        value: Constant::Aggregate(seed_consts),
                    })
                    .with_result(agg),
                );
                for (i, val) in field_vals.iter().enumerate() {
                    // Trust (wave-UF): a unit field is value-less — its `Constant::PhantomData` seed
                    // slot is the final value, so emit no `InsertField` for it.
                    let Some(val) = val else { continue };
                    let next = self.fresh();
                    self.push_node(InstrNode::new(Inst::InsertField {
                            ty: agg_ty.clone(),
                            aggregate: agg,
                            field: i as u32,
                            value: *val,
                        })
                        .with_result(next),
                    );
                    agg = next;
                }
                Some(agg)
            }
            // Trust: field projection. We handle tuple-typed `lhs` (`t.0`, `t.1`, …) AND struct-typed
            // `lhs` (`p.x`) — a tuple value is a `Ty::Tuple` aggregate, a struct value a first-class
            // `Ty::Struct(id)` aggregate; both carry field VALUES in-register (`Aggregate`), so
            // `ExtractField` reads field N directly (the struct's field index is `name.as_u32()`,
            // matching the field-index order `ExprKind::Adt`/`register_struct` build the aggregate
            // in — declaration order). Enums/unions stay fail-closed. `variant_index` is irrelevant
            // for a single-variant struct (variant 0).
            ExprKind::Field { lhs, name, .. } => {
                let lhs = *lhs;
                let field = name.as_u32();
                // Gate on the LHS being a tuple OR a struct; other aggregates are unsupported for now.
                let lhs_kind = self.thir.exprs[lhs].ty.kind();
                let lhs_ok = matches!(lhs_kind, ty::Tuple(_))
                    || matches!(lhs_kind, ty::Adt(adt, _) if adt.is_struct());
                if !lhs_ok {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Field(non-tuple/struct aggregate)"));
                    return None;
                }
                // The field type: a scalar maps directly; a LOCAL struct field is a nested-holder
                // READ (`self.storage.<scalar>` — the read twin of the wave-31 nested assign), so
                // it is built through the SAME deterministic opaque-tolerant builder the write side
                // uses. This yields a registered `Ty::Struct` value whose scalar lanes are reachable
                // by a following `ExtractField`, and — because `register_struct` dedups by `DefId`
                // — read and write agree on the registration. Std containers / enums / non-local
                // structs stay `map_ty`-mapped (→ `Ty::Unit`) and fail closed below.
                let field_ty = match expr_ty.kind() {
                    ty::Adt(a, ga) if a.is_struct() && a.did().is_local() => self
                        .struct_ty_rmw_opaque(*a, *ga, None)
                        .unwrap_or_else(|| self.map_ty(expr_ty)),
                    _ => self.map_ty(expr_ty),
                };
                // The projected field must itself be an interpretable scalar — bools, the
                // fixed-width ints, and (matching the `seed_constant` float admission) f32/f64,
                // whose `ExtractField` reads the `FloatBits` value the aggregate carries — OR a
                // registered `Ty::Struct` holder (the nested-place read link, whose own opaque
                // lanes are `Ty::Unit` and are never read). Fail-closed otherwise.
                let scalar_field = matches!(
                    field_ty,
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
                        | Ty::F32
                        | Ty::F64
                );
                // Trust (wave-31, NESTED places; field-opaque RECONCILED): a STRUCT-typed field
                // read (`s.inner` as an rvalue — the link step of a nested `s.a.b` read chain,
                // and the read side of the wave-31 nested assign) is admitted as a first-class
                // aggregate `ExtractField` when its `Ty::Struct` is registered. The registered
                // build is the deterministic opaque-tolerant one (`struct_ty_rmw_opaque` above),
                // whose opaque `Ty::Unit` lanes are never read, so no pure-value gate is needed.
                // The aggregate model carries nested struct values first-class (wave-12 nested
                // `Constant::Aggregate` seeds; the interpreter materializes `(Ty::Struct,
                // Aggregate)` per-field), so the extraction is value-exact — recursion through
                // `lower_expr(lhs)` then handles arbitrary depth.
                let struct_field = matches!(&field_ty, Ty::Struct(sid)
                    if self.registered_struct_field_tys(*sid).is_some());
                if !(scalar_field || struct_field) {
                    // Trust (wave-EL): a DATA-ENUM field read — the whole-VALUE move-out/copy
                    // `let mut store = reflowed.store;` (and the enum leg of a struct-literal
                    // field / return / call arg). The field's value is the OPAQUE LANE unit
                    // (`ExtractField { ty: Ty::Unit }` of the holder aggregate), the exact
                    // discipline of `read_opaque_option_lane`, generalized from the Option lang
                    // enum to any opaque-lane data enum. FAIL-CLOSED, three gates (all proven,
                    // never assumed): (1) the mapped field type is `Ty::Unit`, (2) the RUSTC
                    // leaf type is an opaque-lane DATA ENUM (`is_opaque_lane_enum` — a Vec, a
                    // `()`, or any other Unit-mapped non-enum keeps declining right below),
                    // (3) the holder's REGISTERED struct places a `Ty::Unit` lane at this index
                    // (so the extract is well-typed and a PROJECTED/differently-registered lane
                    // can never silently read as an opaque unit) — OR, wave-RS, a `Ty::Bool`
                    // OPTION-DISCRIMINANT lane under `TRUST_OPTION_FLAG_LANES=1`: the leaf's
                    // rustc type must additionally be the `Option` lang enum (the EXACT mirror
                    // of the `struct_ty_rmw_opaque` registration arm — a data enum can never
                    // register `Ty::Bool`, so this admits only the wave's own lanes), and the
                    // read is the REAL discriminant value (the write side stores only literal
                    // `Some`/`None` const bools), carried at `Ty::Bool` — this is what makes
                    // `as_mut`/receiver reads of an optflag lane lower instead of regressing
                    // (the measured flag-ON decline this wave retires). `contains_call` is
                    // FORCED for the bool read: the lane is an ABSTRACTION of the Option's
                    // bytes, so the body stays structurally NotRun (CLEAN-ONLY), exactly the
                    // `try_lower_opaque_option_read` posture. Payload EXTRACTION
                    // (match/downcast) never reaches this arm and keeps its own
                    // `EnumMatch(...)` declines.
                    if matches!(field_ty, Ty::Unit) && self.is_opaque_lane_enum(expr_ty) {
                        let holder_lane = match self.thir.exprs[lhs].ty.kind() {
                            ty::Adt(hadt, hargs) if hadt.is_struct() => self
                                .struct_ty_rmw_opaque(*hadt, *hargs, None)
                                .and_then(|t| match t {
                                    Ty::Struct(sid) => self.registered_struct_field_tys(sid),
                                    _ => None,
                                })
                                .and_then(|fts| fts.get(field as usize).cloned()),
                            _ => None,
                        };
                        let is_option_leaf = matches!(expr_ty.kind(), ty::Adt(a, _)
                            if self.tcx.get_diagnostic_item(rustc_span::sym::Option)
                                == Some(a.did()));
                        let lane = match holder_lane {
                            Some(Ty::Unit) => Some(Ty::Unit),
                            Some(Ty::Bool) if option_flag_lanes_enabled() && is_option_leaf => {
                                Some(Ty::Bool)
                            }
                            _ => None,
                        };
                        if let Some(lane_ty) = lane {
                            let agg = match self.lower_expr(lhs) {
                                Some(v) => v,
                                None => {
                                    self.unsupported
                                        .push((format!("{expr_span:?}"), "Field(unsupported lhs)"));
                                    return None;
                                }
                            };
                            if lane_ty == Ty::Bool {
                                self.contains_call = true;
                            }
                            let res = self.fresh();
                            self.push_node(InstrNode::new(Inst::ExtractField {
                                    ty: lane_ty,
                                    aggregate: agg,
                                    field,
                                })
                                .with_result(res),
                            );
                            return Some(res);
                        }
                    }
                    self.unsupported.push((format!("{expr_span:?}"), "Field(non-scalar field ty)"));
                    return None;
                }
                let agg = match self.lower_expr(lhs) {
                    Some(v) => v,
                    None => {
                        self.unsupported.push((format!("{expr_span:?}"), "Field(unsupported lhs)"));
                        return None;
                    }
                };
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::ExtractField { ty: field_ty, aggregate: agg, field })
                        .with_result(res),
                );
                Some(res)
            }
            // Trust: fixed-size array construction `[a, b, c]` → a runtime trust-ir aggregate, built
            // with the SAME machinery as tuples/structs: the array `[T; N]` is represented as a
            // `Ty::Tuple([T; N])` of N IDENTICAL element types (NOT `Ty::Array(TyId, N)`, which needs an
            // interned `TyId` this producer never mints). A `Ty::Tuple` aggregate of scalar elements is
            // what `map_ty`'s array arm produces and what the pinned interpreter materializes
            // (`(Ty::Tuple, Constant::Aggregate)`), so `InsertField` writes each element value over a
            // typed `Const`-aggregate seed exactly as tuple construction does.
            //
            // FAIL-CLOSED: a non-scalar element type (its `seed_constant`/`map_ty` records the gap), an
            // arity mismatch, or any element value that is unsupported / a borrow pointer.
            ExprKind::Array { fields } => {
                let field_ids: Vec<ExprId> = fields.iter().copied().collect();
                // map_ty turns `[T; N]` into `Ty::Tuple([T; N])` for N > 0, and `Ty::Array(TyId, 0)`
                // for the ZERO-LENGTH `[]` (or fails closed to Unit on a bad elem).
                let array_ty = self.map_ty(expr_ty);
                // Trust: `[]` → a single typed empty-array constant. The pinned interpreter
                // materializes `(Ty::Array, Constant::Array)` with an exact length check
                // (scratch-verified, cmtest w4_struct (5)); no seed/InsertField machinery is
                // needed for zero elements. Arity is cross-checked against the mapped length
                // (defensive — both derive from the same rustc type).
                if let Ty::Array(_, n) = &array_ty {
                    if *n != 0 || !field_ids.is_empty() {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Array(len/shape desync)"));
                        return None;
                    }
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: array_ty.clone(),
                            value: Constant::Array(Vec::new()),
                        })
                        .with_result(res),
                    );
                    return Some(res);
                }
                let Ty::Tuple(elem_tys) = array_ty.clone() else {
                    self.unsupported.push((format!("{expr_span:?}"), "Array(non-tuple mapped ty)"));
                    return None;
                };
                if elem_tys.len() != field_ids.len() {
                    self.unsupported.push((format!("{expr_span:?}"), "Array(arity mismatch)"));
                    return None;
                }
                // Lower each element FIRST (fail-closed if any is unsupported — never an aggregate hole).
                let mut elem_vals: Vec<ValueId> = Vec::with_capacity(field_ids.len());
                for f in &field_ids {
                    match self.lower_expr(*f) {
                        Some(v) => {
                            if self.is_borrow_ptr(v) {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Array(borrow ptr element)"));
                                return None;
                            }
                            elem_vals.push(v)
                        }
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Array(unsupported element)"));
                            return None;
                        }
                    }
                }
                self.build_array_aggregate(expr_span, &array_ty, &elem_tys, &elem_vals)
            }
            // Trust: array-repeat construction `[x; N]` → the same `Ty::Tuple([T; N])` aggregate, with
            // the single element value `x` written into ALL N slots. `count` is a `ty::Const`; we read
            // it with `try_to_target_usize` (fail-closed if it is not a concrete usize, e.g. a generic
            // const param). `x` is lowered ONCE and reused for every slot, mirroring Rust's `[x; N]`
            // semantics for a `Copy` element (we only model scalar elements, which are `Copy`).
            //
            // FAIL-CLOSED: a non-evaluable count, a non-scalar element, or an unsupported / borrow-ptr
            // element value.
            ExprKind::Repeat { value, count } => {
                let value = *value;
                let count = *count;
                // Trust (wave-AR): a LARGE constant repeat `[c; N]` (N >= REPEAT_COMPACT_MIN)
                // takes the COMPACT O(N) spelling — ONE `Inst::Const` over a count-based
                // `Ty::Array(TyId, N)` — BEFORE the legacy `Ty::Tuple` machinery below can
                // materialize N element types x N instructions (the measured O(N^2) memory
                // wedge: 1.4GB at N=4096, 5.3GB at 8192, ~100GB for the real aterm-grid
                // `[0; 65536]`). The count probe is side-effect-free, so a non-const count
                // falls through to the legacy path and records exactly the reasons it always
                // did. See `lower_repeat_compact` for the semantics/fail-closed contract.
                if let Some(n) = count.try_to_target_usize(self.tcx) {
                    if n >= REPEAT_COMPACT_MIN {
                        return self.lower_repeat_compact(expr_span, expr_ty, value, n);
                    }
                }
                let array_ty = self.map_ty(expr_ty);
                // Trust: `[x; 0]` → the typed empty-array constant (`Ty::Array(TyId, 0)` — the
                // zero-length `map_ty` spelling). The operand `x` is still LOWERED first (rustc
                // evaluates the repeat operand even for N = 0, so any trap it carries must stay
                // on the path) and its value is then discarded — exactly the old
                // `Ty::Tuple([])`-shaped behavior (elem lowered once, written zero times). The
                // borrow-ptr escape guard is kept (conservative: the value goes nowhere, but a
                // borrow pointer reaching here stays out of scope).
                if let Ty::Array(_, 0) = &array_ty {
                    match self.lower_expr(value) {
                        Some(v) if self.is_borrow_ptr(v) => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Repeat(borrow ptr element)"));
                            return None;
                        }
                        Some(_) => {}
                        None => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Repeat(unsupported element)"));
                            return None;
                        }
                    }
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: array_ty.clone(),
                            value: Constant::Array(Vec::new()),
                        })
                        .with_result(res),
                    );
                    return Some(res);
                }
                let Ty::Tuple(elem_tys) = array_ty.clone() else {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Repeat(non-tuple mapped ty)"));
                    return None;
                };
                // Cross-check the mapped arity against the count (defensive — `map_ty`'s array arm
                // already used this same count to size the tuple).
                let n = match count.try_to_target_usize(self.tcx) {
                    Some(n) => n as usize,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Repeat(non-const count)"));
                        return None;
                    }
                };
                if elem_tys.len() != n {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Repeat(count/arity mismatch)"));
                    return None;
                }
                let elem = match self.lower_expr(value) {
                    Some(v) => {
                        if self.is_borrow_ptr(v) {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Repeat(borrow ptr element)"));
                            return None;
                        }
                        v
                    }
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Repeat(unsupported element)"));
                        return None;
                    }
                };
                // Same value into all N slots.
                let elem_vals: Vec<ValueId> = vec![elem; n];
                self.build_array_aggregate(expr_span, &array_ty, &elem_tys, &elem_vals)
            }
            // Trust: array indexing `arr[i]` (the *non-overloaded* `ExprKind::Index`). The array value
            // is a `Ty::Tuple` aggregate (see the construction arms); indexing reads one element out.
            //   * CONSTANT index `arr[0]` → `Inst::ExtractField` at the literal offset (clean, like a
            //     tuple `.0`). The interpreter's `eval_extract_field` reads aggregate field N directly.
            //   * DYNAMIC index `arr[i]` (runtime `i`) → `Inst::ExtractElement` with the runtime index
            //     `ValueId`. The interpreter's `eval_extract_element` accepts a runtime integer index
            //     over an `Aggregate` value and TRAPS (`UndefinedBehavior`) on out-of-bounds — exactly
            //     MIR's bounds-check-panic semantics, so the bounds obligation is discharged by the
            //     interpreter's OOB trap (no separate `Assert` needed for differential equivalence).
            //
            // FAIL-CLOSED: a non-array `lhs` (slice/`&[T]`/`Vec` — not `ty::Array`), a non-scalar element
            // type, an unsupported `lhs`/`index`, or a borrow-ptr operand.
            ExprKind::Index { lhs, index } => {
                let lhs = *lhs;
                let index = *index;
                let lhs_rty = self.thir.exprs[lhs].ty;
                // SLICE index `s[i]` (FAITHFUL fat-pointer read). The indexed place is a `[T]` slice
                // (the `Deref` of a `&[T]` fat pointer). We read the data pointer out of the slice tuple
                // (`ExtractField 0`), `GEP` to element `i`, and `Load` it. The data pointer addresses an
                // in-memory array of exactly `N` elements (see `lower_array_to_slice`), so an OOB index
                // makes the `Load` trap (`UndefinedBehavior`) — exactly MIR's bounds-check panic, so the
                // bounds obligation is discharged by the interpreter's OOB trap (matching the array path).
                if matches!(lhs_rty.kind(), ty::Slice(_)) {
                    return self.lower_slice_index(expr_span, expr_ty, lhs, index);
                }
                // The indexed base must otherwise be a fixed-size array (`ty::Array`); Vec fails closed.
                if !matches!(lhs_rty.kind(), ty::Array(_, _)) {
                    self.unsupported.push((format!("{expr_span:?}"), "Index(non-array base)"));
                    return None;
                }
                // The element (result) type must be an interpretable scalar (we only build scalar arrays).
                let elem_ty = self.map_ty(expr_ty);
                if !is_scalar_ty(&elem_ty) {
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Index(non-scalar element ty)"));
                    return None;
                }
                let agg = match self.lower_expr(lhs) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Index(unsupported base)"));
                        return None;
                    }
                };
                if self.is_borrow_ptr(agg) {
                    self.unsupported.push((format!("{expr_span:?}"), "Index(borrow ptr base)"));
                    return None;
                }
                // CONSTANT index fast-path: a literal `arr[K]` lowers to `ExtractField K`.
                if let Some(k) = self.const_index_value(index) {
                    let res = self.fresh();
                    self.push_node(InstrNode::new(Inst::ExtractField {
                            ty: elem_ty,
                            aggregate: agg,
                            field: k,
                        })
                        .with_result(res),
                    );
                    return Some(res);
                }
                // DYNAMIC index: lower the runtime index operand and emit `ExtractElement`.
                let idx_val = match self.lower_expr(index) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Index(unsupported index)"));
                        return None;
                    }
                };
                if self.is_borrow_ptr(idx_val) {
                    self.unsupported.push((format!("{expr_span:?}"), "Index(borrow ptr index)"));
                    return None;
                }
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::ExtractElement {
                        ty: elem_ty,
                        array: agg,
                        index: idx_val,
                    })
                    .with_result(res),
                );
                Some(res)
            }
            // Trust: `loop { body }` (and the `while c {b}` / `loop`-without-break-value that desugar
            // to it) → a loop-header block carrying the loop-carried locals as block-params, a back-edge
            // `Br` from the body's fallthrough end, and an exit block reached by `break`. See `lower_loop`.
            ExprKind::Loop { body } => {
                let body = *body;
                // No enclosing `Scope` captured the loop's HirId (uncommon — most `Loop`s are
                // Scope-wrapped). Recover the break/continue label from the body itself.
                let loop_scope = self.loop_body_scope(body);
                self.lower_loop(expr_span, loop_scope, body)
            }
            // Trust: `break` (no value) → branch to the innermost loop's exit, carrying nothing (the
            // exit reads carried locals at their header-param versions). A `break` WITH a value, or a
            // labeled `break 'l` that does not target the innermost loop, is fail-closed.
            ExprKind::Break { label, value } => {
                let label = *label;
                let has_value = value.is_some();
                self.lower_break(expr_span, label, has_value)
            }
            // Trust: `continue` → branch to the innermost loop's header (a back-edge), carrying the
            // loop-carried locals' current values. Labeled `continue 'l` not targeting the innermost
            // loop is fail-closed.
            ExprKind::Continue { label } => {
                let label = *label;
                self.lower_continue(expr_span, label)
            }
            // Trust: SHARED borrow of a LOCAL — `&x` (the memory-model foothold). We materialize a
            // stack slot for the local and store the local's CURRENT SSA value into it, then the
            // borrow's value IS that slot pointer:
            //
            //   %p = Alloca { ty: <local ty> }      ; a fresh slot
            //        Store  { ty: <local ty>, %p, value: <local's current ValueId> }
            //   ⇒ %p : Ty::Ptr
            //
            // For an IMMUTABLE local this single store is correct: the borrow checker guarantees the
            // local cannot change while borrowed, so the slot's contents stay equal to the value that
            // a `*r` would read.
            //
            // MUTABLE borrow `&mut local`: the local was PROMOTED to a memory slot by the pre-pass
            // (it is `&mut`-borrowed here). We yield its EXISTING slot Ptr directly — no fresh
            // Alloca/snapshot Store — so a write through this pointer (`*r = v`) and direct reads of
            // the local (`Load` from the same slot) share one cell. The Ptr is recorded in BOTH
            // `mut_borrow_ptrs` (so the `*r = v` write arm recognizes it) and `borrow_ptrs` (so the
            // existing escape guards still fire). FAIL-CLOSED: a `&mut` of a non-local place
            // (`&mut a.b`, `&mut a[i]`, `&mut *p`) or a local the pre-pass somehow did not promote.
            //
            // The borrowed place is found by the REBORROW PEEL (`reborrow_target`): THIR wraps
            // every reference-typed call arg as `Borrow{kind, Deref{...}}` (`f(&x)` is
            // `Borrow{Shared, Deref{Borrow{Shared, VarRef(x)}}}`), and `*&place == place`, so the
            // peel bottoms out at either the underlying LOCAL (routed to the snapshot/slot paths
            // above) or an existing borrow POINTER (`&*r` — the reborrow IS that pointer). Any
            // borrow whose peel is NOT a local or a producer-made pointer (`&a.b`, `&a[i]`, a
            // raw-ptr deref) fails closed (would need a real address-of, not the snapshot store /
            // slot model). `Shared`/`Fake` are both immutable/aliasable, so both take the
            // snapshot-store path.
            ExprKind::Borrow { borrow_kind, arg } => {
                let arg = *arg;
                // Trust: FAITHFUL `&a[..]` full-range slice. rustc lowers `&a[..]` (a `RangeFull` index
                // on an array) NOT as a clean unsize coercion but as a SHARED borrow of
                // `*<[T] as Index<RangeFull>>::index(&a, ..)` — i.e. `Borrow{Shared, Deref{Call{
                // Index::index, [&a, RangeFull]}}}`, with this borrow's type `&[T]`. The result IS the
                // whole array as a slice, so we synthesize the SAME fat pointer the unsize coercion
                // builds: `(data_ptr = &in-memory-array, len = N)`. This keeps `&a[..]` faithful without
                // routing the library `Index::index` call cross-module. Only a SHARED borrow producing
                // an immutable `&[T]` qualifies; `&mut a[..]` falls through to the fail-closed paths.
                if matches!(
                    borrow_kind,
                    rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_)
                ) && matches!(
                    expr_ty.kind(),
                    ty::Ref(_, p, rustc_hir::Mutability::Not) if matches!(p.kind(), ty::Slice(_))
                ) {
                    if let Some(arr_place) = self.full_range_slice_array(arg) {
                        return self.build_slice_fat_ptr(expr_span, arr_place);
                    }
                }
                let is_mut = matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. });
                if is_mut {
                    // Trust: peel the reborrow shape THIR wraps `&mut` CALL ARGS in
                    // (`Borrow{Mut, Deref{Borrow{Mut, VarRef(x)}}}` — see `reborrow_target`),
                    // then route to the EXISTING promoted-slot admission. The pre-pass already
                    // promotes `x` through this shape (`collect_mut_borrowed_into` descends
                    // into borrow/deref operands and sees the INNER `Borrow{Mut, VarRef(x)}`).
                    let var = match self.reborrow_target(arg, true) {
                        ReborrowTarget::Local(v) => v,
                        ReborrowTarget::Ptr(inner) => {
                            // `&mut *r` / `f(r)` on r: `&mut T` — the mut reborrow of an
                            // existing `&mut` slot pointer IS that pointer (same slot, same
                            // writes; it is already registered in `mut_borrow_ptrs` and
                            // `borrow_ptrs`). Only a pointer this lowering produced (and
                            // registered mutable) qualifies; anything else stays fail-closed.
                            match self.lower_expr(inner) {
                                Some(v) if self.is_mut_borrow_ptr(v) => return Some(v),
                                _ => {
                                    self.unsupported.push((
                                        format!("{expr_span:?}"),
                                        "Borrow(&mut non-local place)",
                                    ));
                                    return None;
                                }
                            }
                        }
                        ReborrowTarget::NotAPlace => {
                            // Trust (wave-DP): `&mut (*self).fieldK` INSIDE a `Deref`/`DerefMut`
                            // ACCESSOR body lowers as the projection WITNESS + interior ptr
                            // (see `try_lower_deref_accessor_interior_mut`); everywhere else a
                            // `&mut` non-local place keeps the fail-closed tag below.
                            if let Some(v) =
                                self.try_lower_deref_accessor_interior_mut(expr_span, expr_ty, arg)
                            {
                                return Some(v);
                            }
                            // `&mut a.b` / `&mut a[i]` / `&mut *p` — a non-local place we cannot promote.
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Borrow(&mut non-local place)"));
                            return None;
                        }
                    };
                    if !self.is_promoted(var) {
                        // The pre-pass promotes every `&mut`-borrowed LOCAL, so an unpromoted local here
                        // means the pre-pass declined it (non-scalar / pointer-flavored). Fail closed.
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Borrow(&mut unpromoted local)"));
                        return None;
                    }
                    let slot = match self.promoted_slot(var) {
                        Some(s) => s,
                        None => {
                            // `&mut` before the local's `let` emitted its slot — rustc rejects use-before-
                            // init, so this is defensive.
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Borrow(&mut slot missing)"));
                            return None;
                        }
                    };
                    self.mut_borrow_ptrs.push(slot);
                    if !self.borrow_ptrs.contains(&slot) {
                        self.borrow_ptrs.push(slot);
                    }
                    return Some(slot);
                }
                if !matches!(
                    borrow_kind,
                    rustc_middle::mir::BorrowKind::Shared | rustc_middle::mir::BorrowKind::Fake(_)
                ) {
                    self.unsupported.push((format!("{expr_span:?}"), "Borrow(other)"));
                    return None;
                }
                // Trust: same reborrow peel on the SHARED side (`f(&x)` / `f(r)` shapes).
                let var = match self.reborrow_target(arg, false) {
                    ReborrowTarget::Local(v) => v,
                    ReborrowTarget::Ptr(inner) => {
                        // `&*r` — the shared reborrow of an existing borrow pointer IS that
                        // pointer (same address; shared, so no writes flow through it — a mut
                        // slot ptr reborrowed shared is read-only downstream by Rust's types).
                        // Only a LEDGER-registered pointer qualifies: one this lowering
                        // produced, or (wave-5) a ref-typed scalar-pointee PARAM registered at
                        // binding — forwarding `g(r)` reborrows the caller's pointer, which IS
                        // that pointer. Anything else (an unregistered `&&T`/`&Struct` param, a
                        // raw ptr) fails this gate.
                        //
                        // Trust (wave-17): OR a FAT shared reference `&str`/`&[T]` — mapped to
                        // `Ty::Tuple([Ptr, I64])`, so it is NEVER in `borrow_ptrs` (the
                        // `matches!(ty, Ty::Ptr)` param-binding gate skips fat refs). `&*s == s`
                        // for a shared reference, so the reborrowed VALUE is the SAME fat tuple —
                        // return it. Load-bearing: before wave-17 a `&str` param was a THIN
                        // borrow-ptr and `take(&*s)` returned it via the `is_borrow_ptr` arm above;
                        // making `&str` fat (to fix the ABI-unfaithful thin-`&str` return) drops it
                        // out of `borrow_ptrs`, so without this arm `take(&*s)` would REGRESS to
                        // fail-closed. Gated strictly on an IMMUTABLE ref to a fat-pointer pointee
                        // (`str`/`[T]`) — exactly the shapes `map_ty` sends to the fat tuple; a
                        // `&mut`/thin/aggregate ref never matches and stays fail-closed.
                        // Trust (B2-3): `ty::Dynamic` joins the fat set — `&dyn Trait`
                        // now maps to first-class `FatPtr(TraitObject)` (map_ty), so a
                        // forwarding reborrow `g(x)` / `&*x` returns the SAME fat value,
                        // exactly the wave-17 `&str`/`&[T]` precedent (pre-B2-3 the thin
                        // `&dyn` param was ledger-registered and forwarded via the
                        // `is_borrow_ptr` arm above; the fat respell moves it here).
                        let fat_shared_ref = matches!(
                            self.thir.exprs[inner].ty.kind(),
                            ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                                if matches!(pointee.kind(), ty::Str | ty::Slice(_) | ty::Dynamic(..))
                        );
                        match self.lower_expr(inner) {
                            Some(v) if self.is_borrow_ptr(v) => return Some(v),
                            Some(v) if fat_shared_ref => return Some(v),
                            _ => {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Borrow(non-local place)"));
                                return None;
                            }
                        }
                    }
                    ReborrowTarget::NotAPlace => {
                        // Trust (wave-16): a rustc-PROMOTED shared borrow of a scalar const-expr —
                        // `fn f()->&'static i32 { &5 }`, `&C`, `&123u8`, `&true`, `&1.5f32`. The
                        // borrowed `arg` const-evals to a scalar, so rustc promotes it to a `'static`
                        // temporary; we mirror that with a module GLOBAL holding the scalar +
                        // `Inst::GlobalAddr` (a `'static` `Ty::Ptr`) instead of the fail-closed tag.
                        // CLEAN-ONLY (never flipped/interpreted). FAIL CLOSED (tag unchanged) on
                        // everything `eval_promotable_scalar` declines — `&param.field`/`&param[i]`
                        // (const-eval fails: base is a runtime place — the CRITICAL safety case),
                        // `&"s"`/`&&T`/reference pointees (scalar gate), `&STATIC` (a `StaticRef`,
                        // not a const), interior-mutable/aggregate pointees, LOCAL consts, generics.
                        if let Some((gty, init)) = self.eval_promotable_scalar(arg) {
                            let idx = self.pending_globals.len();
                            self.pending_globals.push(Global {
                                // Deterministic body-local name; the crate assembler renames it to a
                                // crate-unique deterministic name when it splices the global in.
                                name: format!("__trust_promoted_{idx}"),
                                ty: gty,
                                mutable: false,
                                initializer: Some(init),
                                linkage: Linkage::Internal,
                                tls: None,
                                // No explicit over-alignment: a promoted scalar takes its
                                // type-derived alignment (trust-ir Global.align lane).
                                align: None,
                            });
                            let global = GlobalId::new(idx as u32);
                            let result = self.fresh();
                            self.push_node(InstrNode::new(Inst::GlobalAddr { global }).with_result(result),
                            );
                            // Register the `'static` address so the return-escape guards ADMIT
                            // returning it (via `global_ptrs`) while every OTHER borrow-ptr escape
                            // guard still fails closed on it (via `borrow_ptrs`) — the
                            // `ref_param_ptrs` pattern. NOT `ref_param_ptrs`/`mut_borrow_ptrs`.
                            self.borrow_ptrs.push(result);
                            self.global_ptrs.push(result);
                            return Some(result);
                        }
                        // Trust (wave-CB): a LOCAL named-const / const-block borrow — `&K` (a `const K`
                        // defined in this crate), which `eval_promotable_scalar` declines (its
                        // `def_id.is_local()` gate). rustc does NOT `'static`-promote these — built MIR
                        // is `_2 = const K; _1 = &_2` (a STACK temporary), verified by -Zdump-mir — so
                        // mirror it FAITHFULLY: lower the const to a scalar VALUE (the read path
                        // `lower_named_const` DEFERS a local const, registering a `PendingConst`) and
                        // snapshot it into a slot + borrow, EXACTLY the `&local` scalar snapshot below.
                        // Gated to a peeled `NamedConst`/`ConstBlock` (a pure const value — NOT a runtime
                        // place: `&param.field` is a `Field`, stays with `field_deref_place` / the tag)
                        // whose value maps to an INT/BOOL scalar. CLEAN-ONLY, PROVEN by the EXISTING
                        // pending-const gates: a `PendingConst` forces `NotRun` (differential.rs:125) AND
                        // blocks the flip (flip_registry.rs:124) — so +0 flip / 0 new divergence with no
                        // new gate. An assoc/generic const with non-region args fails to lower here (the
                        // read path can only defer region-only args) and stays fail-closed.
                        if self.is_const_borrow_arg(arg) {
                            let pty = self.map_ty(self.thir.exprs[arg].ty);
                            if matches!(
                                pty,
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
                            ) {
                                if let Some(cval) = self.lower_expr(arg) {
                                    if !self.is_borrow_ptr(cval) {
                                        let ptr = self.fresh();
                                        self.push_node(InstrNode::new(Inst::Alloca {
                                                ty: pty.clone(),
                                                count: None,
                                                align: None,
                                            })
                                            .with_result(ptr),
                                        );
                                        self.push_node(InstrNode::new(Inst::Store {
                                            ty: pty,
                                            ptr,
                                            value: cval,
                                            volatile: false,
                                            align: None,
                                        }));
                                        self.borrow_ptrs.push(ptr);
                                        return Some(ptr);
                                    }
                                }
                            }
                        }
                        // Trust (wave-25/25b, interior shared-borrow return): `&self.field` — a shared
                        // borrow of a pure-value struct field behind a REF PARAM, RETURNED. The base
                        // `pv ∈ ref_param_ptrs` outlives the call, so the return-escape guard admits
                        // the field address — while a `&local` snapshot slot (NOT in `ref_param_ptrs`)
                        // stays fail-closed, so a dangling interior pointer can never escape. CLEAN
                        // ONLY: the comparator fails closed on a projected borrow (`mir_differential`
                        // ~1692) → `NotRun`, never flipped. `is_pure_value_shape` already excludes any
                        // fat/DST field, so the borrowed field's ref is thin (faithful `Ty::Ptr`).
                        //   * offset 0 (wave-25): the field address IS the struct pointer — return `pv`
                        //     verbatim (a tautology; no GEP, no offset value that could be wrong).
                        //   * offset != 0 (wave-25b): the field address is `pv + off` bytes — emit a
                        //     flat-I8 `GEP` (index = the literal byte offset, read ONLY from rustc's
                        //     `layout.fields.offset`), gated on the borrow's own result mapping to a
                        //     thin `Ty::Ptr`, and register the derived ptr in `interior_ptrs`.
                        if let Some((ptr_expr, deref_expr, field)) = self.field_deref_place(arg) {
                            let struct_rty = self.thir.exprs[deref_expr].ty;
                            // Trust (wave-O): gate on the BORROW RESULT being a THIN reference
                            // (`fat_shape(&FieldTy) == Thin`) rather than the whole struct being
                            // pure-value. This admits `&self.field` when the borrowed FIELD's ref is
                            // thin — a scalar, a Sized nested struct, OR a by-value GENERIC param (the
                            // derived `PartialEq::eq(&self.0, ..)` / `Ord::cmp` idiom: `&T` → `Thin`).
                            // `fat_shape` RECURSES, so a FAT field-ref — `&str`/`&[T]`/`&dyn`/`&extern`
                            // OR a custom-DST `&UnsizedAdt` — is `Fat`/`Opaque` and stays fail-closed
                            // (its len/vtable lane cannot live in a thin GEP). More precise than the
                            // old whole-struct `is_pure_value_shape` gate (which rejected a param field
                            // and any mixed struct); the borrow reads ONE field, so only that field's
                            // ref-thinness matters. `field_byte_offset` still fails closed on a generic
                            // MULTI-field struct (unknown layout) → only single-field (offset 0)
                            // generics and fully-concrete layouts admit. A generic body never flips
                            // (NotRun), so a `&Param` a fat monomorphization would widen stays inert.
                            let field_ref_thin = matches!(struct_rty.kind(), ty::Adt(adt, _) if adt.is_struct())
                                && self.fat_shape(expr_ty, &mut Vec::new()) == FatShape::Thin;
                            if field_ref_thin {
                                if let Some(off) = self.field_byte_offset(struct_rty, field) {
                                    if let Some(pv) = self.lower_expr(ptr_expr) {
                                        if self.ref_param_ptrs.contains(&pv) {
                                            if off == 0 {
                                                return Some(pv);
                                            }
                                            // Defense-in-depth: only synthesize the interior ptr when
                                            // the borrow's OWN result type maps to a thin `Ty::Ptr` (a
                                            // fat/DST field-ref maps to a fat tuple and must stay
                                            // fail-closed — a thin-ptr GEP would be ABI-unfaithful).
                                            // Inert today (`is_pure_value_shape` already excludes fat
                                            // fields), but keeps the thin-pointer invariant local.
                                            if matches!(self.map_ty(expr_ty), Ty::Ptr) {
                                                let off_val = self.fresh();
                                                self.push_node(InstrNode::new(Inst::Const {
                                                        ty: Ty::I64,
                                                        value: Constant::Int(off as i128),
                                                    })
                                                    .with_result(off_val),
                                                );
                                                let iptr = self.fresh();
                                                self.push_node(InstrNode::new(Inst::GEP {
                                                        pointee_ty: Ty::I8,
                                                        base: pv,
                                                        indices: vec![off_val],
                                                        inbounds: true,
                                                    })
                                                    .with_result(iptr),
                                                );
                                                // `borrow_ptrs` → every NON-return escape guard fails
                                                // closed on it; `interior_ptrs` → ONLY the two
                                                // return-escape guards admit it (caller memory that
                                                // outlives the call).
                                                self.borrow_ptrs.push(iptr);
                                                self.interior_ptrs.push(iptr);
                                                return Some(iptr);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        // Trust (wave-SB): a scalar-valued borrow whose `arg` reached `NotAPlace` and
                        // was declined by every handler above — the primary target is a NON-const scalar
                        // RVALUE `&(x*2)` / `&(1-1)` / `&(n as f32)` (a temporary rustc promotes to a
                        // stack slot), but a scalar PLACE-projection borrow that also lands here
                        // (`&local.field`, `&arr[i]` — classified `NotAPlace`, not a `field_deref_place`
                        // ref-param interior, not const/static-promotable) is admitted too. Mirror
                        // rustc's promotion with the EXACT wave-CB alloca+store+borrow snapshot over the
                        // arg's scalar VALUE. For a place borrow this snapshots the field/element VALUE
                        // (not its address) — value-sound: a SHARED borrow is read-only, so its only
                        // observable is the Deref-`Load` (identical value), and any address-dependent use
                        // fails closed via the escape guards below. This unblocks the `assert_eq!(x*2, y)`
                        // family (`&(x*2)` was the sole gap) plus scalar `&local.field`/`&arr[i]` asserts.
                        // Every one of these was `Borrow(non-local place)` (dirty) before, so
                        // became_dirty == 0. SOUND:
                        //   * the snapshot ptr enters `borrow_ptrs` ONLY (NOT `ref_param_ptrs` /
                        //     `global_ptrs` / `interior_ptrs`), so every escape guard (return / aggregate
                        //     / binop) fails closed — a non-place rvalue slot dies with the frame and can
                        //     never escape as a dangling ref (borrowck forbids returning it anyway);
                        //   * its only non-failing use is a Deref-`Load`, which round-trips the EXACT
                        //     stored scalar; the comparator value-folds through the store/load (agreeing
                        //     with built-MIR's own temp-promotion `_1 = x*2; _2 = &_1`) or fails closed →
                        //     `NotRun`. So it is faithful even if flipped and can never yield a wrong
                        //     value; the `assert_eq!` idiom additionally carries a cold `assert_failed`
                        //     call → `NotRun`. `lower_expr(arg)` failing records its own precise gap and
                        //     falls through to the tag below (masking, unchanged).
                        let arg_ty = self.map_ty(self.thir.exprs[arg].ty);
                        if matches!(
                            arg_ty,
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
                                | Ty::F32
                                | Ty::F64
                        ) {
                            if let Some(cval) = self.lower_expr(arg) {
                                if !self.is_borrow_ptr(cval) {
                                    let ptr = self.fresh();
                                    self.push_node(InstrNode::new(Inst::Alloca {
                                            ty: arg_ty.clone(),
                                            count: None,
                                            align: None,
                                        })
                                        .with_result(ptr),
                                    );
                                    self.push_node(InstrNode::new(Inst::Store {
                                        ty: arg_ty,
                                        ptr,
                                        value: cval,
                                        volatile: false,
                                        align: None,
                                    }));
                                    self.borrow_ptrs.push(ptr);
                                    return Some(ptr);
                                }
                            }
                        }
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Borrow(non-local place)"));
                        return None;
                    }
                };
                // The local's CURRENT value + declared `Ty`. A memory-PROMOTED local (it is
                // `&mut`-borrowed elsewhere in the body) lives in its slot, not the SSA env —
                // `Load` the slot for the snapshot value (the slot is the local's single source
                // of truth, so the load IS its current value; the borrow checker keeps it frozen
                // for the shared borrow's lifetime, so the snapshot proof below still holds).
                let (cur_val, pointee_ty) = if self.is_promoted(var) {
                    match (self.promoted_slot(var), self.promoted_ty(var)) {
                        (Some(slot), Some(pty)) => {
                            let cur = self.fresh();
                            self.push_node(InstrNode::new(Inst::Load {
                                    ty: pty.clone(),
                                    ptr: slot,
                                    volatile: false,
                                    align: None,
                                })
                                .with_result(cur),
                            );
                            (cur, pty)
                        }
                        _ => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Borrow(unbound local)"));
                            return None;
                        }
                    }
                } else {
                    // The local must be live (bound) and have a recorded `Ty` (its declared type).
                    match (self.local_value(var), self.local_ty(var)) {
                        (Some(v), Some(t)) => (v, t),
                        _ => {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Borrow(unbound local)"));
                            return None;
                        }
                    }
                };
                // Only borrow scalars: the slot store/load round-trips a scalar value through memory.
                // Aggregates/pointers as pointees are out of scope (fail-closed).
                if !matches!(
                    pointee_ty,
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
                ) {
                    self.unsupported.push((format!("{expr_span:?}"), "Borrow(non-scalar pointee)"));
                    return None;
                }
                // Refuse to borrow something that is itself a borrow pointer (`&&x` / `&r`): that would
                // store a `Ty::Ptr` into the slot, escaping the immediate-deref-only contract.
                if self.is_borrow_ptr(cur_val) {
                    self.unsupported.push((format!("{expr_span:?}"), "Borrow(of a borrow ptr)"));
                    return None;
                }
                let ptr = self.fresh();
                self.push_node(InstrNode::new(Inst::Alloca {
                        ty: pointee_ty.clone(),
                        count: None,
                        align: None,
                    })
                    .with_result(ptr),
                );
                self.push_node(InstrNode::new(Inst::Store {
                    ty: pointee_ty,
                    ptr,
                    value: cur_val,
                    volatile: false,
                    align: None,
                }));
                self.borrow_ptrs.push(ptr);
                Some(ptr)
            }
            // Trust: non-overloaded `*r` (the consume side of the foothold). `r` must lower to a
            // borrow-produced `Ty::Ptr`; we `Load` the pointee type (this expr's type) from it:
            //
            //   %v = Load { ty: <*r's type>, %p }
            //
            // FAIL-CLOSED if `arg` does not lower to a value, or lowers to a value that is NOT a known
            // borrow pointer (e.g. a raw pointer, an unregistered `&&T`/non-scalar-pointee param) —
            // only a LEDGER-registered pointer can be soundly loaded here: one the `Borrow` arm
            // produced, or (wave-5) a ref-typed scalar-pointee PARAM registered at binding (`*r` on
            // `fn f(r: &i32)` — the Load reads the CALLER's slot, the memory model unchanged).
            ExprKind::Deref { arg } => {
                let arg = *arg;
                let ptr = match self.lower_expr(arg) {
                    Some(v) => v,
                    None => {
                        self.unsupported.push((format!("{expr_span:?}"), "Deref(arg no value)"));
                        return None;
                    }
                };
                if !self.is_borrow_ptr(ptr) {
                    self.unsupported.push((format!("{expr_span:?}"), "Deref(non-borrow ptr)"));
                    return None;
                }
                // A whole-struct `*self` read routes through the SAME opaque-tolerant builder the
                // `(*p).field = v` write uses (`written_field = None`): a sibling the method never
                // touches that is non-pure/unmappable (a `Vec`/`Option<T>`/data-enum — the real
                // `GridStorage` shape) becomes an opaque `Ty::Unit` lane instead of recording a
                // coverage gap, and — critically — read and write agree on the per-body struct
                // registration (dedup by `DefId`), so the `ExtractField`/`InsertField` indices stay
                // in lock-step. A pure-value struct maps identically to plain `map_ty`, and a
                // non-struct pointee falls through to plain `map_ty` unchanged.
                let pointee_ty = match expr_ty.kind() {
                    ty::Adt(adt, gargs) if adt.is_struct() => self
                        .struct_ty_rmw_opaque(*adt, *gargs, None)
                        .unwrap_or_else(|| self.map_ty(expr_ty)),
                    _ => self.map_ty(expr_ty),
                };
                // Trust (wave-11 D2): a `*r` read of a SCALAR pointee loads the scalar; a read of a
                // REGISTERED AGGREGATE pointee (`Ty::Struct(id)`/`Ty::Tuple`) loads the whole
                // aggregate VALUE. `map_ty` yields `Ty::Struct(id)` for any recursively-registerable
                // struct (fields may be nested aggregates, registered depth-first); a struct with an
                // unmappable field falls back to `Ty::Unit` + a `Ty(struct-fields)` tag, so it does
                // not reach here as `Ty::Struct`. This unblocks `*r` whole-aggregate reads (the #1
                // bounded sole-blocker, `Deref(non-scalar pointee)`) and `s.field` where `s = *self`
                // (the `Field` arm then `ExtractField`s the scalar leaf; nested `s.a.b` chains
                // through the Field arm's wave-31 registered-pure-value-struct link admission,
                // one `ExtractField` per level). CLEAN-RATE ONLY / NO MISCOMPILE: the LOAD-BEARING
                // invariant is that the shim (`to_mir.rs`) fails closed on EVERY aggregate `Load`
                // regardless of field shape — a struct/tuple borrow ptr is only ever an opaque
                // ref-param pointer (struct-LOCAL borrows fail the Borrow scalar gate), rejected by
                // the shim's opaque-params arm, and a non-scalar load-result local is rejected by the
                // `scalar_ty` funnel — so these bodies never flip. In the interpreter differential
                // they are structurally `NotRun` (the Load READS the ref param → `param_never_read`
                // is false), so they are never interpreted → 0 divergence by construction. A
                // non-aggregate non-scalar pointee (raw ptr, `&&T`, `Ty::Ptr`) stays fail-closed.
                let pointee_ok = matches!(
                    pointee_ty,
                    Ty::Bool | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
                        | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
                        | Ty::Isize | Ty::Usize | Ty::Char
                    // Trust (B2-2): a FAT-POINTER pointee (`*r` where `r: &&str`/`&&[T]`)
                    // Loads the 16-byte two-lane fat value — the interpreter's B2
                    // memory arms execute it (byte layout + decode). Pre-B2 the same
                    // shape passed as the Ty::Tuple pointee; admitting FatPtr restores
                    // exactly that class on the new spelling.
                    // Trust (B2-3): KIND-gated to the length-metadata kinds. A
                    // TraitObject pointee (`**r` on `&&dyn`) is excluded this slice —
                    // no legitimate dyn fat value can reach memory yet (construction
                    // is fail-closed), so admitting it would only ever Load garbage.
                    | Ty::FatPtr(trust_ir::FatPtrKind::Slice(_) | trust_ir::FatPtrKind::Str)
                    // Trust (B3-2a): a FIRST-CLASS enum pointee (`*r` on `&E`) — the
                    // B2-2 lesson replayed on the new type: pre-flip these pointees
                    // rode the legacy Tuple admission; the interpreter round-trips
                    // Ty::Enum values through memory (B3-1's pinned tests), so the
                    // Load is executable. Excluding it regressed 15 clean bodies.
                    | Ty::Enum(_)
                ) || matches!(pointee_ty, Ty::Struct(_) | Ty::Tuple(_));
                if !pointee_ok {
                    self.unsupported.push((format!("{expr_span:?}"), "Deref(non-scalar pointee)"));
                    return None;
                }
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::Load {
                        ty: pointee_ty,
                        ptr,
                        volatile: false,
                        align: None,
                    })
                    .with_result(res),
                );
                Some(res)
            }
            // Trust: unary `!a` / `-a` on a SCALAR (bool / fixed-width int). Both lower to a single
            // `Inst::UnOp` over the (recursively lowered) operand:
            //   * `!a`  → `UnOp::Not`. For an integer this is bitwise NOT (the interpreter computes
            //     `!raw` then masks to the operand width); for a `bool` it is logical NOT. Note the
            //     trust-ir interpreter's `eval_int_unop` masks the result to the type width, so a
            //     `bool` `Not` must be typed `Ty::Bool` (the interpreter reads bool operands as a
            //     0/1 integer there). We pass the operand's mapped scalar `Ty`, so bool stays bool.
            //   * `-a`  → under `overflow_checks()`, the CHECKED-NEG idiom `Const MIN; ICmp
            //     Ne(a, MIN); Assert; UnOp::Neg` — mirroring built MIR's exact shape (rustc
            //     inserts `assert(a != MIN, OverflowNeg)` as a SEPARATE statement before the
            //     plain `Rvalue::UnaryOp(Neg)`, which the MIR-side oracle lowers faithfully via
            //     its Terminator::Assert arm). Trust (wave-NEG): the previous plain-`Neg`-only
            //     model deliberately skipped the `-MIN` trap "because the differential's
            //     oracle-incapacity skip covers the MIN sample" — TRUE until B9-B1b made those
            //     oracles interpretable, whereupon the differential caught the model returning
            //     the WRAPPED value where built semantics PANIC (the first real catch;
            //     tests/ui/frontmatter/location-include-in-item-ctxt.rs::foo). trust-ir's
            //     `OverflowOp` still has no Neg form and none is needed: the separate-assert
            //     idiom is the faithful spelling on BOTH sides. Checks OFF → plain wrapping
            //     `UnOp::Neg`, matching MIR's release shape.
            //
            // FAIL-CLOSED: a `Deref` unary (`*p` is `ExprKind::Deref`, not `Unary`, so never reaches
            // here), a non-scalar operand type, or an operand that does not lower to a value.
            ExprKind::Unary { op, arg } => {
                let arg = *arg;
                // `-a` requires a signed integer; `!a` accepts bool or any int. Operand type drives it.
                let operand_rty = self.thir.exprs[arg].ty;
                let ty = self.map_ty(expr_ty);
                // Trust: floats join the admitted operand set for `-a` only (see the `Neg` arm
                // below); `!a` has no float form in Rust, and the interpreter's float unop path
                // rejects `Not` anyway — fail closed defensively.
                let is_float = matches!(ty, Ty::F32 | Ty::F64);
                if !is_scalar_ty(&ty) && !is_float {
                    self.unsupported.push((format!("{expr_span:?}"), "Unary(non-scalar operand)"));
                    return None;
                }
                // Validate the op and reject malformed shapes BEFORE lowering the operand.
                match op {
                    MirUnOp::Not => {
                        if is_float {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Unary(Not on float)"));
                            return None;
                        }
                    }
                    MirUnOp::Neg => {
                        // `-a` is only defined on signed integers and floats in this slice; an
                        // unsigned or bool `Neg` would be a malformed shape (rustc never produces
                        // it for these types), so fail closed rather than emit a wrong op.
                        if !matches!(operand_rty.kind(), ty::Int(_) | ty::Float(_)) {
                            self.unsupported
                                .push((format!("{expr_span:?}"), "Unary(Neg non-signed-int)"));
                            return None;
                        }
                    }
                    // `*p` is `ExprKind::Deref` and `PtrMetadata` is a MIR-only runtime op; neither
                    // surfaces as a THIR `ExprKind::Unary`, but guard defensively.
                    MirUnOp::PtrMetadata => {
                        self.unsupported.push((format!("{expr_span:?}"), "Unary(PtrMetadata)"));
                        return None;
                    }
                }
                let operand = self.lower_expr(arg)?;
                if self.is_borrow_ptr(operand) {
                    self.unsupported.push((format!("{expr_span:?}"), "Unary(borrow ptr operand)"));
                    return None;
                }
                let res = self.fresh();
                // Trust: `!b` on a `bool` cannot use `Inst::UnOp { Not }` — the pinned trust-ir
                // interpreter's `eval_unop` routes every non-float scalar through `expect_int_value`,
                // which REJECTS a `Ty::Bool` operand (a bool is only readable via `as_bool`, in
                // Assert/Assume/Select/CondBr). This is the same asymmetry the overflow-assert path
                // documents above. So logical-not is `Select(b ? false : true)` — interpretable and
                // exactly `!b`. Integer `!a` (bitwise not) DOES go through `UnOp::Not` (the interpreter
                // computes `!raw` then masks to width); only the bool case needs the `Select` form.
                if matches!(op, MirUnOp::Not) && ty == Ty::Bool {
                    let false_const = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                            .with_result(false_const),
                    );
                    let true_const = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                            .with_result(true_const),
                    );
                    self.push_node(InstrNode::new(Inst::Select {
                            ty: Ty::Bool,
                            cond: operand,
                            then_val: false_const,
                            else_val: true_const,
                        })
                        .with_result(res),
                    );
                    return Some(res);
                }
                // Trust (wave-NEG): signed-int negation under overflow checks gets the
                // checked-neg guard `Assert(a != MIN)` BEFORE the wrapping Neg — built MIR's
                // exact separate-assert shape (AssertKind::OverflowNeg), the div-guard template
                // verbatim (Const + ICmp Ne + Assert, all interpreter-native). Floats are total
                // (FNeg below); unsigned/bool Neg was rejected above. Checks OFF → plain Neg.
                if matches!(op, MirUnOp::Neg) && !is_float && self.tcx.sess.overflow_checks() {
                    if let Some(min) = int_min_value(&ty) {
                        let min_c = self.fresh();
                        self.push_node(InstrNode::new(Inst::Const {
                                ty: ty.clone(),
                                value: Constant::Int(min),
                            })
                            .with_result(min_c),
                        );
                        let ok = self.fresh();
                        self.push_node(InstrNode::new(Inst::ICmp {
                                op: ICmpOp::Ne,
                                ty: ty.clone(),
                                lhs: operand,
                                rhs: min_c,
                            })
                            .with_result(ok),
                        );
                        self.push_node(InstrNode::new(Inst::Assert { cond: ok })
                                .with_proof(ProofAnnotation::NoOverflow),
                        );
                    } else {
                        // A signed-int Neg whose MIN is not spellable would be a malformed
                        // width — fail closed rather than emit an unguarded Neg.
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Unary(Neg width unguardable)"));
                        return None;
                    }
                }
                let un = match op {
                    MirUnOp::Not => UnOp::Not,
                    // Trust: float negation is `UnOp::FNeg` (the IEEE sign-bit flip; total, no
                    // overflow guard — `-f32::MIN` is finite and `-NaN` flips the payload sign
                    // bit) — exactly the MIR-side oracle's mapping (trust-ir-bridge
                    // lower.rs:12893: `UnOp::Neg` on a float operand → `TrustIrUnOp::FNeg`).
                    // Integer `Neg` pairs the plain `UnOp::Neg` with the wave-NEG guard above.
                    MirUnOp::Neg if is_float => UnOp::FNeg,
                    MirUnOp::Neg => UnOp::Neg,
                    MirUnOp::PtrMetadata => unreachable!("PtrMetadata handled above"),
                };
                self.push_node(InstrNode::new(Inst::UnOp { op: un, ty, operand }).with_result(res));
                Some(res)
            }
            // Trust: ARRAY-TO-SLICE unsizing coercion `&[T; N] → &[T]` (the FAITHFUL slice path).
            // rustc inserts this as a `PointerCoercion { cast: Unsize, source }` adjustment over a
            // shared borrow of an array (e.g. `let s: &[i32] = &a;`). We lower it to a real fat pointer
            // `Ty::Tuple([Ty::Ptr, Ty::I64]) = (data_ptr, len)`: the array is `Alloca`'d + `Store`'d in
            // memory and `data_ptr` is its REAL address (not a placeholder), `len` is the static `N`.
            // See `lower_array_to_slice` for the construction. A later `s[i]` reads `GEP(data_ptr, i)`
            // + `Load`; a `s.len()` reads `ExtractField(slice, 1)`.
            //
            // FAIL-CLOSED: any other `PointerCoercion` (`ReifyFnPointer`, `MutToConstPointer`,
            // `ArrayToPointer`, `DynStar`, or an `Unsize` to a trait object / a `&mut [T]` slice) — only
            // the array→shared-slice unsize is modeled; everything else records `unsupported`.
            ExprKind::PointerCoercion { cast: PointerCoercion::Unsize, source, .. } => {
                let source = *source;
                // Trust (B2-3): the dyn→dyn IDENTITY re-coercion. A `&dyn Trait` type
                // carries its region bound (`dyn Trait + 'r`), so rustc respells EVERY
                // fresh-region reborrow of a `&dyn` value — most commonly passing a
                // `&dyn` param straight through to a `&dyn` callee arg (`g(d)`) — as a
                // `PointerCoercion::Unsize` node, even though no unsizing occurs: with
                // the SAME principal on both sides the value is the SAME 16-byte fat
                // pair (`&*d == d` for a shared ref — the wave-17 fat_shared_ref
                // argument, surfacing at the coercion node). Gate on MAPPED-TYPE
                // equality at the fat trait-object spelling: same trait_id ⇒ same
                // principal def path (collisions fail the mint), which excludes trait
                // UPCASTING (`&dyn Sub → &dyn Super` CHANGES the vtable lane at
                // runtime — an identity pass-through would sign the wrong metadata) and
                // excludes any fail-closed mint (`Ty::Unit` never equals a FatPtr).
                // The source lowers through the ordinary Borrow/reborrow lanes, so the
                // fat value itself is produced by the existing forwarding machinery.
                let dyn_identity = matches!(
                    expr_ty.kind(),
                    ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                        if matches!(pointee.kind(), ty::Dynamic(..))
                ) && matches!(
                    self.thir.exprs[source].ty.kind(),
                    ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                        if matches!(pointee.kind(), ty::Dynamic(..))
                );
                if dyn_identity {
                    let target_fat = self.map_ty(expr_ty);
                    let source_fat = self.map_ty(self.thir.exprs[source].ty);
                    if matches!(target_fat, Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. }))
                        && target_fat == source_fat
                    {
                        return self.lower_expr(source);
                    }
                    self.unsupported.push((format!("{expr_span:?}"), "Unsize(dyn upcast)"));
                    return None;
                }
                // Only the `&[T; N] → &[T]` unsize is faithful here: this expr's type must be `&[T]`.
                let is_slice_ref = matches!(
                    expr_ty.kind(),
                    ty::Ref(_, pointee, rustc_hir::Mutability::Not)
                        if matches!(pointee.kind(), ty::Slice(_))
                );
                if !is_slice_ref {
                    self.unsupported.push((format!("{expr_span:?}"), "Unsize(non-slice target)"));
                    return None;
                }
                self.lower_array_to_slice(expr_span, source)
            }
            // Trust: FN-ITEM → FN-POINTER reification (`let f: fn(i32) -> i32 = double;`).
            // The source is a ZST of `ty::FnDef` type; the value is a first-class function
            // constant: `Inst::Const { ty: Ty::Func(sig), value: Constant::FnDef(func_id) }`,
            // with `func_id` DefIndex-derived and LEDGERED exactly like an `Inst::Call` callee
            // (`admit_callee`), so crate-level assembly rewrites it to the spliced target's
            // dense id or fail-closes it onto a bodyless declaration. The only consumer of the
            // value inside the fragment is `Inst::CallIndirect` (see the Call arm).
            //
            // FAIL-CLOSED (`resolve_reify_target`): generic fn items, closure-likes,
            // trait-default bodies, `#[track_caller]`/shim targets (`resolve_for_fn_ptr`
            // surfaces those as `ReifyShim`), non-`Fn`/`AssocFn` def-kinds — plus an
            // unmappable fn-ptr signature (`map_ty` → "Ty(fn-ptr)").
            ExprKind::PointerCoercion {
                cast: PointerCoercion::ReifyFnPointer(_), source, ..
            } => {
                let mut src = *source;
                // The coercion's TARGET type is this expr's type — must map to Ty::Func.
                let fnptr_ty = self.map_ty(expr_ty);
                let Ty::Func(_) = fnptr_ty else {
                    // `map_ty` already recorded the precise "Ty(fn-ptr)" gap.
                    self.unsupported
                        .push((format!("{expr_span:?}"), "Reify(unsupported fn-ptr ty)"));
                    return None;
                };
                loop {
                    match &self.thir.exprs[src].kind {
                        ExprKind::Scope { value, .. } => src = *value,
                        ExprKind::Use { source } => src = *source,
                        _ => break,
                    }
                }
                let (def_id, gen_args) = match self.thir.exprs[src].ty.kind() {
                    ty::FnDef(d, a) => (*d, *a),
                    _ => {
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Reify(non-fn-def source)"));
                        return None;
                    }
                };
                match self.resolve_reify_target(def_id, gen_args) {
                    Ok(resolved) => {
                        let func_id = self.admit_callee(resolved);
                        let res = self.fresh();
                        self.push_node(InstrNode::new(Inst::Const {
                                ty: fnptr_ty,
                                value: Constant::FnDef(func_id),
                            })
                            .with_result(res),
                        );
                        Some(res)
                    }
                    Err(tag) => {
                        self.unsupported.push((format!("{expr_span:?}"), tag));
                        None
                    }
                }
            }
            ExprKind::PointerCoercion { .. } => {
                self.unsupported
                    .push((format!("{expr_span:?}"), "PointerCoercion(non-array-unsize)"));
                None
            }
            // Trust: a numeric `as` cast `a as T` (`ExprKind::Cast { source }`; the target is THIS
            // expr's type). We lower it to a single `Inst::Cast` whose `CastOp` is chosen from the
            // (source, destination) scalar CLASSES — int / bool / float — matching rustc's `as`:
            //
            //   integer-shaped → integer-shaped (`Ty::Char` participates with a 32-bit unsigned
            //   carrier while retaining its distinct type identity):
            //     * dst < src            → `Trunc`  (drop the high bits; interpreter masks)
            //     * dst > src, src signed → `SExt`   (sign-extend)
            //     * dst > src, src unsigned → `ZExt` (zero-extend)
            //     * dst == src           → `Trunc` (identity at equal width — an `i32 as u32` /
            //       `u8 as i8` reinterpretation the interpreter re-types).
            //   bool → int  → `ZExt`   (bool is a 1-bit unsigned 0/1; `bool as uN/iN` is MIR
            //     `IntToInt`, a zero-extension — always widening).
            //   int → float → `SIToFP`/`UIToFP` by source signedness (MIR `IntToFloat`;
            //     round-to-nearest, never traps/saturates — LLVM si/uitofp == Rust `as`).
            //   float → float → `FPExt` (widen, exact) / `FPTrunc` (narrow, round-nearest) —
            //     MIR `FloatToFloat`, both matching Rust `as`.
            //
            // FAIL-CLOSED, with a PRECISE tag, for the cases that are NOT a faithful single op:
            //   * float → int (`Cast(float→int saturating)`): MIR `FloatToInt` is lowered by rustc
            //     CODEGEN to a saturating clamp + NaN→0; trust-ir's `FPToSI/FPToUI` are documented
            //     LLVM-raw (non-saturating), so emitting them would be a miscompile, not a fallback.
            //   * pointer / fn-pointer operand (`Cast(ptr source)` / borrow-ptr / `Cast(ptr dest)`):
            //     provenance is not modeled.
            //   * anything else non-scalar (enum-discriminant, aggregate): `Cast(non-int source)` /
            //     `Cast(non-int dest)`.
            // A non-`Cast` `as`-like coercion (`PointerCoercion`, `Use`) never reaches here.
            ExprKind::Cast { source } => {
                let source = *source;
                let src_rty = self.thir.exprs[source].ty;
                let src_ty = self.map_ty(src_rty);
                let dst_ty = self.map_ty(expr_ty);
                let src_int = int_scalar_bits(&src_ty);
                let dst_int = int_scalar_bits(&dst_ty);
                let src_float = float_scalar_bits(&src_ty);
                let dst_float = float_scalar_bits(&dst_ty);
                let src_bool = matches!(src_ty, Ty::Bool);

                let cast_op = if let (Some((src_bits, src_signed)), Some((dst_bits, _))) =
                    (src_int, dst_int)
                {
                    // Integer-shaped → integer-shaped; `Ty::Char` retains its type identity.
                    if dst_bits < src_bits {
                        CastOp::Trunc
                    } else if dst_bits > src_bits {
                        if src_signed { CastOp::SExt } else { CastOp::ZExt }
                    } else {
                        CastOp::Trunc
                    }
                } else if src_bool && dst_int.is_some() {
                    // bool → int: zero-extend the 1-bit value (MIR `IntToInt`).
                    CastOp::ZExt
                } else if let (Some((_, src_signed)), Some(_)) = (src_int, dst_float) {
                    // int → float (MIR `IntToFloat`).
                    if src_signed { CastOp::SIToFP } else { CastOp::UIToFP }
                } else if let (Some(src_fb), Some(dst_fb)) = (src_float, dst_float) {
                    // float → float (MIR `FloatToFloat`). f32/f64 are the only floats, so the
                    // widths always differ: wider dst ⇒ extend, narrower dst ⇒ truncate.
                    if dst_fb > src_fb { CastOp::FPExt } else { CastOp::FPTrunc }
                } else if let (Some(_), Some((_, dst_signed))) = (src_float, dst_int) {
                    // float → int. Rust's `f as iN`/`uN` is SATURATING (stabilized
                    // 1.45): NaN→0 and out-of-range magnitudes clamp to the
                    // destination's [MIN,MAX], lowered by codegen to LLVM
                    // fptosi.sat/fptoui.sat. Emit the dedicated saturating trust-ir
                    // op (raw FPToSI/FPToUI is UB on overflow). src_float is Some
                    // only for f32/f64 (float_scalar_bits), so f16/f128 sources
                    // fall through to the precise-tag fail-closed arm below.
                    if dst_signed { CastOp::FPToSISat } else { CastOp::FPToUISat }
                } else {
                    // Everything else: classify the offending side precisely.
                    let tag = if matches!(src_rty.kind(), ty::RawPtr(..) | ty::Ref(..)) {
                        "Cast(ptr source)"
                    } else if matches!(expr_ty.kind(), ty::RawPtr(..) | ty::Ref(..)) {
                        "Cast(ptr dest)"
                    } else if src_int.is_none() && !src_bool && src_float.is_none() {
                        "Cast(non-int source)"
                    } else {
                        "Cast(non-int dest)"
                    };
                    self.unsupported.push((format!("{expr_span:?}"), tag));
                    return None;
                };
                let operand = self.lower_expr(source)?;
                if self.is_borrow_ptr(operand) {
                    self.unsupported.push((format!("{expr_span:?}"), "Cast(borrow ptr operand)"));
                    return None;
                }
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::Cast { op: cast_op, src_ty, dst_ty, operand })
                        .with_result(res),
                );
                Some(res)
            }
            // Trust: a NAMED constant — `i32::MAX`, a user `const` item, an associated const. It
            // names a `(DefId, GenericArgsRef)` the compiler's const machinery can evaluate; we
            // resolve + evaluate it with `const_eval_resolve_for_typeck` (the same valtree query
            // pattern matching uses) and admit ONLY scalar integer/bool results as `Inst::Const`.
            // A LOCAL scalar const is not evaluated here (reentrancy) — it emits a sentinel
            // placeholder plus a `PendingConst` record the `crate_module` finalizer patches.
            // FAIL-CLOSED (`lower_named_const`): a non-scalar result type (float/char/aggregate/
            // reference/str), still-generic args (a `T::MAX` in a generic body), or any evaluation
            // error — recorded with a precise tag, never a guessed value.
            ExprKind::NamedConst { def_id, args, .. } => {
                let def_id = *def_id;
                let args = *args;
                self.lower_named_const(
                    expr_span,
                    expr_ty,
                    def_id,
                    args,
                    "NamedConst(non-scalar)",
                    "NamedConst(eval failed)",
                    "NamedConst(local, deferred)",
                )
            }
            // Trust (wave-SR2): a `static` READ. `ExprKind::StaticRef` is a LITERAL holding the
            // ADDRESS of a `static` item (rustc thir.rs: "A literal containing the address of a
            // `static`"), so the enclosing `Deref` is what reads the value. Mirror the wave-16
            // promoted-borrow lane exactly: emit a body-scoped IMMUTABLE global carrying the
            // static's const-evaluated initializer and return `Inst::GlobalAddr` (a `'static`
            // `Ty::Ptr`); the surrounding `Deref` then `Load`s through it, and `&STATIC`
            // (`Borrow{Deref{StaticRef}}`) collapses to the same pointer by the reborrow rule.
            //
            // Deduped per DefId (the `symbolic_consts` precedent): every read of one static
            // resolves to the SAME `GlobalId`, so read-read equality is structural rather than
            // coincidental.
            //
            // FAIL CLOSED (tag "StaticRef(...)", never a guessed address) on everything whose
            // value an immutable global cannot faithfully stand for:
            //   * `static mut` — a mutable static's reads are ordered against writes we do not
            //     model; promoting it to an immutable global would license constant-folding a
            //     value that changes;
            //   * `#[thread_local]` — one address per thread, not one global;
            //   * a NON-`Freeze` type (interior mutability: `AtomicUsize`, `Cell`, …) — same
            //     reason as `static mut`, and the wave-16 lane already refuses these;
            //   * a LOCAL static — evaluating its initializer from inside `mir_built` re-enters
            //     the query stack (the E0391 hazard `lower_named_const` defers around); this
            //     first slice admits only non-local statics, exactly like
            //     `eval_nonlocal_scalar_const`;
            //   * an extern/foreign static (no initializer) and any initializer outside the
            //     admitted scalar set.
            // Trust (wave-CP): a CONST-GENERIC PARAMETER read — `fn f<const N: usize>() -> usize
            // { N }`. Pre-monomorphization `N` has no value, which is EXACTLY what the
            // `symbolic_consts` lane already models for `B::BOOL`-style param-bearing assoc
            // consts: one body-scoped EXTERN IMMUTABLE global (`initializer: None`,
            // `Linkage::External` — trust-ir's native "declared, value unknown" vocabulary),
            // read via `GlobalAddr` + `Load`, deduped per param DefId so repeated reads of the
            // same `N` Load the SAME global and read-read equality is structural.
            //
            // The body becomes SYMBOLIC (`Lowered::symbolic`), which the existing seams already
            // enforce: excluded from the interpretation differential (a value-less Load would
            // manufacture a false TypeError-vs-value verdict) and from the crate-module splice
            // (the assembled executable module must never carry value-less globals). This buys
            // COVERAGE, not Agreed — and that exclusion is what keeps the claim honest.
            ExprKind::ConstParam { def_id, .. } => {
                let def_id = *def_id;
                self.lower_const_param(expr_span, expr_ty, def_id)
            }
            ExprKind::StaticRef { def_id, .. } => {
                let def_id = *def_id;
                self.lower_static_ref(expr_span, expr_ty, def_id)
            }
            // Trust: an inline `const { … }` block. Structurally identical to `NamedConst` — a
            // `(DefId, GenericArgsRef)` naming an (anonymous) evaluable constant — so it shares the
            // exact same const-eval path and scalar-only admission gate, with its own reason tags.
            ExprKind::ConstBlock { did, args } => {
                let did = *did;
                let args = *args;
                self.lower_named_const(
                    expr_span,
                    expr_ty,
                    did,
                    args,
                    "ConstBlock(non-scalar)",
                    "ConstBlock(eval failed)",
                    "ConstBlock(local, deferred)",
                )
            }
            // Trust (wave-CF): a CAPTURING Fn/FnMut closure LITERAL in value position (`let f =
            // || x+1`). Materialize the env as a `Ty::Tuple(captures)` VALUE (capture order = field
            // index) — the SAME model wave-CE's `UpvarRef` read side uses through the `&{closure}`
            // env ptr, and the one `map_ty` signs the closure local with. Build it as a typed
            // aggregate SEED (Ptr lanes = `PhantomData`, scalar lanes = their zero — every lane
            // overwritten below) + one `InsertField` per lowered capture operand (`closure.upvars`,
            // in field order: a by-REF capture lowers to a `Ty::Ptr` borrow, a `move` capture to a
            // scalar). The enclosing fn then borrows this local and passes it to the ClosureCall
            // (see that arm). CLEAN-ONLY: the enclosing fn contains the closure CALL → the
            // interpreter differential bails (`contains_call` → `NotRun`) so the env is never
            // interpreted; and the shim fails closed on the non-scalar env `Const`-aggregate /
            // `Alloca{Ty::Tuple}` → the body never flips. FAIL CLOSED on: a coroutine/async literal
            // (`expr_ty` not `ty::Closure`), a `FnOnce` by-value env, a capture-free closure
            // (wave-5 skips its binding; a non-skipped value-position one is out of scope), a
            // non-thin capture (keeps the env tuple table-free/spliceable), an operand/count
            // mismatch, or a capture operand that itself fails to lower.
            ExprKind::Closure(closure) => {
                let upvar_ids: Vec<ExprId> = closure.upvars.iter().copied().collect();
                let ty::Closure(_, cargs) = expr_ty.kind() else {
                    self.unsupported.push((format!("{expr_span:?}"), "Closure(value position)"));
                    return None;
                };
                let clo = cargs.as_closure();
                let upvar_tys = clo.upvar_tys();
                if upvar_tys.is_empty()
                    || matches!(clo.kind(), ty::ClosureKind::FnOnce)
                    || upvar_ids.len() != upvar_tys.len()
                    || !upvar_tys.iter().all(|t| self.upvar_is_thin(t))
                {
                    self.unsupported.push((format!("{expr_span:?}"), "Closure(value position)"));
                    return None;
                }
                // `elem_tys` is built exactly as `map_ty(closure)` builds it (same order, same
                // per-capture `map_ty`), so the closure local's declared type (recorded via
                // `map_ty` at the `let` binding) matches this constructed value.
                let elem_tys: Vec<Ty> = upvar_tys.iter().map(|t| self.map_ty(t)).collect();
                let env_ty = Ty::Tuple(elem_tys.clone());
                // Seed: Ptr lanes = `PhantomData` (the sole type-agnostic Ptr-lane constant, as in
                // `build_fat_ptr_from_parts`), scalar lanes = `seed_constant`'s zero. Every lane is
                // overwritten by an `InsertField` below.
                let mut seed_consts = Vec::with_capacity(elem_tys.len());
                for t in &elem_tys {
                    let c = match t {
                        Ty::Ptr => Constant::PhantomData,
                        _ => match seed_constant(t) {
                            Some(c) => c,
                            None => {
                                self.unsupported
                                    .push((format!("{expr_span:?}"), "Closure(value position)"));
                                return None;
                            }
                        },
                    };
                    seed_consts.push(c);
                }
                let mut agg = self.fresh();
                self.push_node(InstrNode::new(Inst::Const {
                        ty: env_ty.clone(),
                        value: Constant::Aggregate(seed_consts),
                    })
                    .with_result(agg),
                );
                for (i, upvar_id) in upvar_ids.iter().enumerate() {
                    let Some(val) = self.lower_expr(*upvar_id) else {
                        // The capture operand's own fail-closed tag is already recorded; decline
                        // the whole env so the closure local stays unbound (the call fails closed).
                        self.unsupported
                            .push((format!("{expr_span:?}"), "Closure(value position)"));
                        return None;
                    };
                    let next = self.fresh();
                    self.push_node(InstrNode::new(Inst::InsertField {
                            ty: env_ty.clone(),
                            aggregate: agg,
                            field: i as u32,
                            value: val,
                        })
                        .with_result(next),
                    );
                    agg = next;
                }
                Some(agg)
            }
            other => {
                self.unsupported.push((format!("{expr_span:?}"), variant_name(other)));
                None
            }
        }
    }

    /// Trust: emit a (non-comparison) binary operation with the EXACT MIR-faithful safety-check
    /// sequence rustc's `build_binary_op` emits (compiler/rustc_mir_build/src/builder/expr/
    /// as_rvalue.rs:437-587), so the producer, the MIR-side bridge, and real MIR agree on which
    /// inputs trap. Shared by `ExprKind::Binary` and `ExprKind::AssignOp` (rustc routes both
    /// through the same `build_binary_op`). `ty` is the mapped operand/result type, `signed` the
    /// OPERAND signedness (from the lhs rustc type), `rhs_rty` the shift amount's rustc type (only
    /// read for `<<`/`>>`). The checks, in MIR's exact order and gating:
    ///
    ///   * `+`/`-`/`*` (int, `overflow_checks()` ON): `Inst::Overflow` (a `(result, overflowed)`
    ///     pair) + `Assert(!overflowed)` — mirrors `AddWithOverflow` + `AssertKind::Overflow`.
    ///     Annotation `NoOverflow` (what the bridge's `assert_proof_annotation` attaches).
    ///   * `/`/`%` (int, UNCONDITIONAL — MIR always checks division, even with overflow checks
    ///     off): `Assert(rhs != 0)` — mirrors `AssertKind::DivisionByZero`/`RemainderByZero`
    ///     (annotation `DivNonZero`) — then, for SIGNED operands only (also unconditional),
    ///     `Assert(rhs != -1 || lhs != MIN)` — mirrors the `(rhs == -1) & (lhs == MIN)`
    ///     `AssertKind::Overflow(Div|Rem)` check (annotation `NoOverflow`). MIR composes the two
    ///     equalities with a bool `BitAnd`; a bool `BinOp`/`UnOp::Not` is not interpretable in
    ///     trust-ir (`eval_binop`/`eval_unop` `expect_int_value` their operands — the same
    ///     asymmetry the overflow-assert path documents), so we emit the equivalent
    ///     `Ne`-comparisons joined by a `Select` disjunction: the assert holds/fails on exactly
    ///     the same inputs.
    ///   * `<<`/`>>` (int, `overflow_checks()` ON): reinterpret the shift amount as its UNSIGNED
    ///     same-width type (an equal-width `Trunc`, matching MIR's `IntToInt` cast — a negative
    ///     signed amount becomes huge unsigned) and `Assert(amount_u < LHS_BITS)` — mirrors
    ///     MIR's `Lt` + `AssertKind::Overflow(Shl|Shr)` (annotation `ShiftInRange`).
    ///   * everything else (bitwise ops; the overflow-checks-off `+`/`-`/`*` and `<<`/`>>`):
    ///     the plain wrapping `Inst::BinOp`.
    ///
    /// The plain `BinOp` op is SIGNEDNESS-CORRECT: `SDiv`/`UDiv`, `SRem`/`URem`, `AShr`/`LShr`
    /// chosen by the operand signedness (mirroring the bridge's `map_binop`); the old
    /// sign-oblivious mapping (`Div → SDiv` even for `u32`) was a real mis-lowering, fixed here.
    /// Emitting the asserts BEFORE the op also matters for the differential: both sides then trap
    /// with the SAME code (`Panic` from the assert) instead of the THIR side reaching the op's
    /// internal `UndefinedBehavior` trap while the oracle panics at its MIR assert.
    #[allow(clippy::too_many_arguments)]
    fn emit_arith_binop(
        &mut self,
        span: rustc_span::Span,
        op: MirBinOp,
        ty: Ty,
        signed: bool,
        rhs_rty: RustcTy<'tcx>,
        l: ValueId,
        r: ValueId,
    ) -> Option<ValueId> {
        // Trust: FLOAT arithmetic first — floats do NOT trap, so none of the integer
        // overflow/div-zero/shift-range machinery below applies (MIR gates every one of those
        // asserts on `ty.is_integral()`, as_rvalue.rs:449/473/522 — a float `+`/`/`/`%` is a
        // plain `BinaryOp` even with overflow checks on, and `1.0/0.0` is IEEE infinity, not a
        // panic). Route to the trap-free `FAdd`-family emitter; letting a float fall through to
        // the integer `map_binop` fall-through would emit an integer `Add` over float operands
        // (a type error the interpreter rejects), so the intercept is mandatory, not cosmetic.
        // This also covers `ExprKind::AssignOp` (`x += 1.0`), which shares this emitter.
        if matches!(ty, Ty::F32 | Ty::F64) {
            return self.emit_float_binop(span, op, ty, l, r);
        }
        // Trust: `ty` here is the *mapped* `trust_ir::Ty`. `isize`/`usize` were mapped by `map_ty`
        // to their platform fixed-width equivalent (e.g. I64/U64 on a 64-bit target), so they fall
        // into the fixed-width arms below and are checked exactly like the other ints — matching
        // MIR, which checks pointer-width ints too.
        let is_int = matches!(
            ty,
            Ty::I8
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
        );
        // P1.1: integer `+`/`-`/`*` must mirror MIR's overflow semantics, not wrapping `BinOp`.
        // When overflow checks are on, rustc lowers `a + b` to `AddWithOverflow` (a
        // `(result, overflowed)` pair) followed by an `Assert { !overflowed }`
        // (`AssertKind::Overflow`). We reproduce that with `Inst::Overflow` + an overflow
        // `Inst::Assert`, so an overflowing input traps on BOTH sides instead of the THIR side
        // silently returning the wrapped value. When overflow checks are OFF (release-like), MIR
        // emits a plain wrapping `BinaryOp`; we match THAT with the plain `BinOp` at the bottom.
        if let Some(ov) = map_overflow_op(op) {
            if self.tcx.sess.overflow_checks() && is_int {
                let res = self.fresh();
                let overflowed = self.fresh();
                // `Inst::Overflow` → (result, overflowed: bool). `ty` carries the integer
                // width+signedness the interpreter needs to decide overflow.
                self.push_node(InstrNode::new(Inst::Overflow { op: ov, ty: ty.clone(), lhs: l, rhs: r })
                        .with_results([res, overflowed]),
                );
                // Assert no overflow, mirroring MIR's `assert(overflowed == false)`. We need the
                // boolean `!overflowed` as the assert condition. The trust-ir interpreter only
                // reads a `bool` operand via `as_bool` (Assert/Assume/Select/CondBr); it does NOT
                // accept `bool` operands to `ICmp`/`UnOp::Not` (those expect integers — see
                // trust-ir `eval_icmp`/`eval_unop` → `expect_int_value`). So we negate via
                // `Select(overflowed ? false : true)`, which is interpretable and gives the same
                // trap-iff-overflow semantics as MIR's overflow assert.
                let ok = self.emit_bool_not(overflowed);
                self.push_node(InstrNode::new(Inst::Assert { cond: ok })
                        .with_proof(ProofAnnotation::NoOverflow),
                );
                return Some(res);
            }
        }
        // Integer `/`/`%`: the UNCONDITIONAL divisor-nonzero assert, then (signed only, also
        // unconditional) the MIN/-1 overflow assert, then the wrapping op — MIR's exact shape.
        if matches!(op, MirBinOp::Div | MirBinOp::Rem) && is_int {
            // `Assert(rhs != 0)` — MIR computes `is_zero = Eq(rhs, 0)` and asserts it FALSE; the
            // `Ne` form is the same predicate with the interpretable polarity (no bool negation).
            let zero_c = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(0) })
                    .with_result(zero_c),
            );
            let nonzero = self.fresh();
            self.push_node(InstrNode::new(Inst::ICmp { op: ICmpOp::Ne, ty: ty.clone(), lhs: r, rhs: zero_c })
                    .with_result(nonzero),
            );
            self.push_node(InstrNode::new(Inst::Assert { cond: nonzero })
                    .with_proof(ProofAnnotation::DivNonZero),
            );
            if signed {
                // `Assert(rhs != -1 || lhs != MIN)` ≡ MIR's `assert(!((rhs == -1) & (lhs ==
                // MIN)))`. `int_min_value` is total on the signed widths; the `if let` is
                // defensive only (an unsigned `ty` cannot reach here with `signed` set).
                if let Some(min) = int_min_value(&ty) {
                    let neg1_c = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(-1) })
                            .with_result(neg1_c),
                    );
                    let min_c = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(min) })
                            .with_result(min_c),
                    );
                    let not_neg1 = self.fresh();
                    self.push_node(InstrNode::new(Inst::ICmp {
                            op: ICmpOp::Ne,
                            ty: ty.clone(),
                            lhs: r,
                            rhs: neg1_c,
                        })
                        .with_result(not_neg1),
                    );
                    let not_min = self.fresh();
                    self.push_node(InstrNode::new(Inst::ICmp {
                            op: ICmpOp::Ne,
                            ty: ty.clone(),
                            lhs: l,
                            rhs: min_c,
                        })
                        .with_result(not_min),
                    );
                    // Disjunction via `Select` (bool `BinOp::Or` is not interpretable):
                    // `ok = not_neg1 ? true : not_min`.
                    let true_c = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                            .with_result(true_c),
                    );
                    let ok = self.fresh();
                    self.push_node(InstrNode::new(Inst::Select {
                            ty: Ty::Bool,
                            cond: not_neg1,
                            then_val: true_c,
                            else_val: not_min,
                        })
                        .with_result(ok),
                    );
                    self.push_node(InstrNode::new(Inst::Assert { cond: ok })
                            .with_proof(ProofAnnotation::NoOverflow),
                    );
                }
            }
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::BinOp { op: map_binop(op, signed), ty, lhs: l, rhs: r })
                    .with_result(res),
            );
            return Some(res);
        }
        // Integer `<<`/`>>` under overflow checks: `Assert(amount_u < LHS_BITS)` with the amount
        // reinterpreted as its unsigned same-width type (MIR's `IntToInt` cast + `Lt` + overflow
        // assert, as_rvalue.rs:473-521). With checks OFF, MIR emits the plain `BinaryOp` — matched
        // by the fall-through below.
        if matches!(op, MirBinOp::Shl | MirBinOp::Shr) && is_int && self.tcx.sess.overflow_checks()
        {
            let rhs_ty = self.map_ty(rhs_rty);
            // The shift amount must itself be a mappable fixed-width integer (always true for
            // valid Rust; `map_ty` records its own gap otherwise). Fail closed defensively.
            let (_, rhs_signed) = match int_scalar_bits(&rhs_ty) {
                Some(v) => v,
                None => {
                    self.unsupported.push((format!("{span:?}"), "Shift(non-int amount)"));
                    return None;
                }
            };
            let (amount_u, u_ty) = if rhs_signed {
                // Equal-width `Trunc` is the bit-pattern reinterpretation (see the
                // `ExprKind::Cast` arm): a negative amount becomes at least 128 unsigned, an
                // overflowing shift for every width — exactly MIR's cast rationale.
                let u_ty = match unsigned_twin(&rhs_ty) {
                    Some(t) => t,
                    None => {
                        self.unsupported.push((format!("{span:?}"), "Shift(non-int amount)"));
                        return None;
                    }
                };
                let cast = self.fresh();
                self.push_node(InstrNode::new(Inst::Cast {
                        op: CastOp::Trunc,
                        src_ty: rhs_ty.clone(),
                        dst_ty: u_ty.clone(),
                        operand: r,
                    })
                    .with_result(cast),
                );
                (cast, u_ty)
            } else {
                (r, rhs_ty.clone())
            };
            // `is_int` guarantees `int_scalar_bits(&ty)` is `Some`; 0 is the defensive fallback.
            let lhs_bits = int_scalar_bits(&ty).map(|(b, _)| b).unwrap_or(0) as i128;
            let bits_c = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: u_ty.clone(), value: Constant::Int(lhs_bits) })
                    .with_result(bits_c),
            );
            let inbounds = self.fresh();
            self.push_node(InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: u_ty.clone(),
                    lhs: amount_u,
                    rhs: bits_c,
                })
                .with_result(inbounds),
            );
            self.push_node(InstrNode::new(Inst::Assert { cond: inbounds })
                    .with_proof(ProofAnnotation::ShiftInRange),
            );
            // Trust: the shift `BinOp`'s AMOUNT must be typed `ty` — trust-ir's `eval_binop`
            // `expect_ty`s BOTH operands against the instruction type, while Rust (and MIR)
            // let the amount keep its own integer type. This was the wave-2
            // `allowed_slices::D0` defect (`const D0: u32 = (1 << 16) | 1`): the emitted
            // `shl u32` carried the i32-typed amount and the interpreter type-errored where
            // the MIR oracle computed the correct u32. Reuse the range check's unsigned
            // reinterpretation when it already lands on `ty` (u32 lhs + i32 literal amount —
            // the common case, no extra instruction), otherwise emit the value-preserving
            // int cast. The amount was JUST asserted `< LHS_BITS`, so the cast preserves the
            // numeric value on every non-trapping path.
            let amount_v = if rhs_ty == ty {
                r
            } else if u_ty == ty {
                amount_u
            } else {
                match self.emit_shift_amount_cast(ty.clone(), rhs_ty, r) {
                    Some(v) => v,
                    None => {
                        self.unsupported.push((format!("{span:?}"), "Shift(non-int amount)"));
                        return None;
                    }
                }
            };
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::BinOp {
                    op: map_binop(op, signed),
                    ty,
                    lhs: l,
                    rhs: amount_v,
                })
                .with_result(res),
            );
            return Some(res);
        }
        // Trust: checks-OFF shifts (MIR emits the plain `BinaryOp` — the checks-ON arm above
        // already returned) still need the AMOUNT typed `ty`; only the value cast is added
        // (no assert, matching MIR). See the checks-ON arm for the `eval_binop` contract.
        let r = if matches!(op, MirBinOp::Shl | MirBinOp::Shr) && is_int {
            let rhs_ty = self.map_ty(rhs_rty);
            if rhs_ty == ty {
                r
            } else {
                match self.emit_shift_amount_cast(ty.clone(), rhs_ty, r) {
                    Some(v) => v,
                    None => {
                        self.unsupported.push((format!("{span:?}"), "Shift(non-int amount)"));
                        return None;
                    }
                }
            }
        } else {
            r
        };
        // Bitwise ops and every overflow-checks-off path: the plain wrapping `BinOp` (MIR's `_`
        // arm in `build_binary_op`).
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::BinOp { op: map_binop(op, signed), ty, lhs: l, rhs: r })
                .with_result(res),
        );
        Some(res)
    }

    /// Trust: emit the value-preserving integer cast of a SHIFT AMOUNT `v` from `src_ty` to the
    /// shifted operand's type `dst_ty` (both fixed-width ints), returning the casted `ValueId`.
    /// Op choice mirrors the `ExprKind::Cast` arm: equal-width or narrowing → `Trunc` (the bit
    /// reinterpretation), widening → `SExt`/`ZExt` by SOURCE signedness (Rust `as` semantics).
    /// An IN-RANGE amount (`0 <= amount < LHS_BITS`; `LHS_BITS <= 128` fits every integer
    /// width) is numerically preserved by every arm. An OUT-of-range amount either already
    /// trapped at the shift-range assert (overflow checks ON), or is UB in Rust (checks OFF —
    /// and the trust-ir interpreter's `shift_amount` guard traps on its own there, so no
    /// defined execution diverges). `None` (caller tags fail-closed) if either type is not a
    /// fixed-width integer.
    fn emit_shift_amount_cast(&mut self, dst_ty: Ty, src_ty: Ty, v: ValueId) -> Option<ValueId> {
        let (src_bits, src_signed) = int_scalar_bits(&src_ty)?;
        let (dst_bits, _) = int_scalar_bits(&dst_ty)?;
        let op = if dst_bits <= src_bits {
            CastOp::Trunc
        } else if src_signed {
            CastOp::SExt
        } else {
            CastOp::ZExt
        };
        let res = self.fresh();
        self.cur
            .push(InstrNode::new(Inst::Cast { op, src_ty, dst_ty, operand: v }).with_result(res));
        Some(res)
    }

    /// Trust: emit a FLOAT arithmetic `Inst::BinOp` — the trap-free IEEE-754 op family
    /// (`FAdd`/`FSub`/`FMul`/`FDiv`/`FRem`), mirroring the MIR-side oracle's `map_float_binop`
    /// arithmetic table (trust-ir-bridge lower.rs:357-361) exactly. No asserts are emitted:
    /// floats never trap (division by zero is IEEE infinity/NaN, overflow saturates to
    /// infinity), and MIR emits the plain `BinaryOp` for float ops regardless of the
    /// overflow-checks setting. The pinned interpreter evaluates these natively in the operand
    /// width (`eval_float_binop` computes in f32 for `Ty::F32`, f64 for `Ty::F64` — the exact
    /// hardware semantics rustc compiles to), so both differential sides produce identical bit
    /// patterns, NaN payloads included. FAIL-CLOSED: any non-arithmetic op on a float (bitwise/
    /// shift — unreachable from typeck'd Rust; `Cmp` — never a THIR `Binary` on primitives)
    /// records a precise tag rather than guessing an integer op.
    fn emit_float_binop(
        &mut self,
        span: rustc_span::Span,
        op: MirBinOp,
        ty: Ty,
        l: ValueId,
        r: ValueId,
    ) -> Option<ValueId> {
        let fop = match op {
            MirBinOp::Add => BinOp::FAdd,
            MirBinOp::Sub => BinOp::FSub,
            MirBinOp::Mul => BinOp::FMul,
            MirBinOp::Div => BinOp::FDiv,
            MirBinOp::Rem => BinOp::FRem,
            _ => {
                self.unsupported.push((format!("{span:?}"), "Binary(float unsupported op)"));
                return None;
            }
        };
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::BinOp { op: fop, ty, lhs: l, rhs: r }).with_result(res));
        Some(res)
    }

    /// Trust: emit the interpretable boolean negation `Select(cond ? false : true)` of a `Bool`
    /// value and return the result. The trust-ir interpreter reads `bool`s only via `as_bool`
    /// (Assert/Assume/Select/CondBr) — `ICmp`/`UnOp::Not` `expect_int_value` — so this `Select`
    /// form is the producer's canonical `!b`.
    fn emit_bool_not(&mut self, cond: ValueId) -> ValueId {
        let false_const = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(false) })
                .with_result(false_const),
        );
        let true_const = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(true_const),
        );
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Select {
                ty: Ty::Bool,
                cond,
                then_val: false_const,
                else_val: true_const,
            })
            .with_result(res),
        );
        res
    }

    /// Trust: lower compound assignment `lhs op= rhs` (`ExprKind::AssignOp`) as the MIR-faithful
    /// read-binop-write, sharing `emit_arith_binop` with `ExprKind::Binary` so `x += e` traps on
    /// exactly the inputs `x = x + e` does (overflow/div-zero/MIN÷-1/shift-range asserts included).
    ///
    /// OPERAND ORDER mirrors rustc's `stmt_expr` AssignOp lowering (rustc_mir_build/src/builder/
    /// expr/stmt.rs:59-94): the RHS is evaluated FIRST, then the LHS place is read (`Operand::Copy`
    /// of the place AFTER the rhs's side effects — the `x += { x += 1; x }` order), then the binop
    /// runs and the result is written back to the place.
    ///
    /// Three place forms, matching `ExprKind::Assign`'s split:
    ///   * a bare SSA LOCAL — read `local_value`, compute, `set_local` the result (the SSA rebind);
    ///   * a memory-PROMOTED local — `Load` its slot, compute, `Store` the result back;
    ///   * a `*r` DEREF of a known `&mut` slot pointer — `Load` through it, compute, `Store` back
    ///     (the same recognizer/guards as the `*r = v` write arm).
    ///
    /// FAIL-CLOSED: any other place (field/index projection), a deref of a non-`&mut`-borrow
    /// pointer, a non-scalar deref/promoted pointee, an unbound local, a borrow-ptr operand, or an
    /// rhs/op that does not lower — each with its own greppable reason tag. `AssignOp` is a
    /// STATEMENT (unit-typed), so it produces no value (`None`), like `Assign`.
    fn lower_assign_op(
        &mut self,
        span: rustc_span::Span,
        op: MirAssignOp,
        lhs: ExprId,
        rhs: ExprId,
    ) -> Option<ValueId> {
        // The underlying binary op — the exact conversion MIR building uses (`op.into()`).
        let bin_op = MirBinOp::from(op);
        let lhs_rty = self.thir.exprs[lhs].ty;
        let rhs_rty = self.thir.exprs[rhs].ty;
        let ty = self.map_ty(lhs_rty);
        let signed = matches!(lhs_rty.kind(), ty::Int(_));

        // `*r op= v` — compound assignment THROUGH a `&mut` pointer.
        if let Some(deref_arg) = self.deref_place_arg(lhs) {
            // RHS first (MIR order), then the pointer place.
            let r = match self.lower_expr(rhs) {
                Some(v) => v,
                None => {
                    self.unsupported.push((format!("{span:?}"), "AssignOp(rhs no value)"));
                    return None;
                }
            };
            if self.is_borrow_ptr(r) {
                self.unsupported.push((format!("{span:?}"), "AssignOp(borrow ptr rhs)"));
                return None;
            }
            let ptr = match self.lower_expr(deref_arg) {
                Some(p) => p,
                None => {
                    self.unsupported.push((format!("{span:?}"), "AssignOp(*r ptr no value)"));
                    return None;
                }
            };
            if !self.is_mut_borrow_ptr(ptr) {
                self.unsupported.push((format!("{span:?}"), "AssignOp(*r non-mut-borrow ptr)"));
                return None;
            }
            if !is_scalar_ty(&ty) {
                self.unsupported.push((format!("{span:?}"), "AssignOp(*r non-scalar)"));
                return None;
            }
            // Read-modify-write through the slot: Load, checked binop, Store.
            let cur = self.fresh();
            self.push_node(InstrNode::new(Inst::Load { ty: ty.clone(), ptr, volatile: false, align: None })
                    .with_result(cur),
            );
            let result =
                self.emit_arith_binop(span, bin_op, ty.clone(), signed, rhs_rty, cur, r)?;
            self.push_node(InstrNode::new(Inst::Store {
                ty,
                ptr,
                value: result,
                volatile: false,
                align: None,
            }));
            return None;
        }

        // Trust (wave-23): `(*p).field op= v` — a scalar COMPOUND field store through a `&mut
        // Struct` ptr (the ref-escape memory model). Whole-struct read-modify-write of the sole
        // changed lane: `Load(*p)`, `ExtractField` the current field scalar, the checked binop,
        // `InsertField` the result over the same lane, `Store(*p)`. Same `NotRun`/never-flip posture
        // as the plain `(*p).field = v` store (the `Load` reads the ref param; the shim fails closed
        // on the opaque-param `Load`/`Store`). `ty` (= `map_ty(lhs_rty)`, the field place type) is
        // the field scalar and `signed` already matches it.
        if let Some((ptr_expr, deref_expr, field)) = self.field_deref_place(lhs) {
            let pointee_rty = self.thir.exprs[deref_expr].ty;
            // Sibling fields the method never touches may be NON-pure-value; they become opaque
            // placeholders (see `struct_ty_rmw_opaque`). The WRITTEN field (`ty`, checked scalar by
            // the helper) is the sole materialized lane. `ty` remains the ExtractField/InsertField
            // scalar type used below.
            let (adt, gargs) = match pointee_rty.kind() {
                ty::Adt(adt, gargs) if adt.is_struct() => (*adt, *gargs),
                _ => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field non-struct pointee)"));
                    return None;
                }
            };
            let struct_ty = match self.struct_ty_rmw_opaque(adt, gargs, Some(field)) {
                Some(t) => t,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field non-scalar field)"));
                    return None;
                }
            };
            // RHS first (MIR order for compound assign), then the ptr place.
            let r = match self.lower_expr(rhs) {
                Some(v) => v,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field rhs no value)"));
                    return None;
                }
            };
            if self.is_borrow_ptr(r) {
                self.unsupported.push((format!("{span:?}"), "AssignOp((*p).field borrow ptr rhs)"));
                return None;
            }
            let ptr = match self.lower_expr(ptr_expr) {
                Some(p) => p,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field ptr no value)"));
                    return None;
                }
            };
            if !self.is_mut_borrow_ptr(ptr) {
                self.unsupported
                    .push((format!("{span:?}"), "AssignOp((*p).field non-mut-borrow ptr)"));
                return None;
            }
            let agg = self.fresh();
            self.push_node(InstrNode::new(Inst::Load {
                    ty: struct_ty.clone(),
                    ptr,
                    volatile: false,
                    align: None,
                })
                .with_result(agg),
            );
            let cur = self.fresh();
            self.push_node(InstrNode::new(Inst::ExtractField { ty: ty.clone(), aggregate: agg, field })
                    .with_result(cur),
            );
            let result =
                self.emit_arith_binop(span, bin_op, ty.clone(), signed, rhs_rty, cur, r)?;
            let newagg = self.fresh();
            self.push_node(InstrNode::new(Inst::InsertField {
                    ty: struct_ty.clone(),
                    aggregate: agg,
                    field,
                    value: result,
                })
                .with_result(newagg),
            );
            self.push_node(InstrNode::new(Inst::Store {
                ty: struct_ty,
                ptr,
                value: newagg,
                volatile: false,
                align: None,
            }));
            return None;
        }

        // Trust (realbody): `(*p).f1.….fk op= v` — a TWO-LEVEL (nested) scalar COMPOUND field store,
        // the chain-generalization of the `(*p).field op= v` arm above (`self.storage.content_gen += 1`
        // — the real GridStorage shape). Resolve the nested place via `field_chain_deref_place` (the
        // same walker the two-level plain-assign uses), build the whole-struct opaque RMW type, walk
        // the REGISTERED field types down the chain (intermediate links must be `Ty::Struct` holders,
        // the leaf a genuine scalar), then read-modify-write the leaf: `Load(*p)`, `ExtractField` DOWN
        // to the leaf scalar, the checked binop, `InsertField` the result back UP the chain, `Store(*p)`.
        // Same `NotRun`/never-flip posture as the one-level arm (the `Load` reads the opaque `&mut`-param
        // pointee; the interpreter shim fails closed on it). A one-level place is handled by the arm
        // above (its `field_deref_place` returns first), so this runs for genuinely nested places.
        if let Some((ptr_expr, deref_expr, chain)) = self.field_chain_deref_place(lhs) {
            let pointee_rty = self.thir.exprs[deref_expr].ty;
            let (adt, gargs) = match pointee_rty.kind() {
                ty::Adt(adt, gargs) if adt.is_struct() => (*adt, *gargs),
                _ => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field non-struct pointee)"));
                    return None;
                }
            };
            let struct_ty = match self.struct_ty_rmw_opaque(adt, gargs, None) {
                Some(t) => t,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field non-scalar field)"));
                    return None;
                }
            };
            // Walk the registered field types down the chain (mirrors the plain-assign chain arm):
            // every intermediate link is a `Ty::Struct` holder; the leaf must be a genuine scalar.
            let mut agg_tys: Vec<Ty> = vec![struct_ty.clone()];
            for k in 0..chain.len() {
                let Ty::Struct(sid) = agg_tys[k] else {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp(nested non-struct link)"));
                    return None;
                };
                let fts = match self.registered_struct_field_tys(sid) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{span:?}"), "AssignOp(nested unregistered link)"));
                        return None;
                    }
                };
                let field_ty = match fts.get(chain[k].1 as usize) {
                    Some(t) => t.clone(),
                    None => {
                        self.unsupported
                            .push((format!("{span:?}"), "AssignOp(nested field index oob)"));
                        return None;
                    }
                };
                if k + 1 < chain.len() {
                    if !matches!(field_ty, Ty::Struct(_)) {
                        self.unsupported
                            .push((format!("{span:?}"), "AssignOp(nested non-struct link)"));
                        return None;
                    }
                    agg_tys.push(field_ty);
                } else if !is_scalar_ty(&field_ty) {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field non-scalar field)"));
                    return None;
                }
            }
            // RHS first (MIR order for compound assign), then the ptr place.
            let r = match self.lower_expr(rhs) {
                Some(v) => v,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field rhs no value)"));
                    return None;
                }
            };
            if self.is_borrow_ptr(r) {
                self.unsupported.push((format!("{span:?}"), "AssignOp((*p).field borrow ptr rhs)"));
                return None;
            }
            let ptr = match self.lower_expr(ptr_expr) {
                Some(p) => p,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "AssignOp((*p).field ptr no value)"));
                    return None;
                }
            };
            if !self.is_mut_borrow_ptr(ptr) {
                self.unsupported
                    .push((format!("{span:?}"), "AssignOp((*p).field non-mut-borrow ptr)"));
                return None;
            }
            // Load the root, extract DOWN to the leaf's parent aggregate.
            let root = self.fresh();
            self.push_node(InstrNode::new(Inst::Load {
                    ty: struct_ty.clone(),
                    ptr,
                    volatile: false,
                    align: None,
                })
                .with_result(root),
            );
            let mut aggs: Vec<ValueId> = vec![root];
            for i in 0..chain.len() - 1 {
                let sub = self.fresh();
                self.push_node(InstrNode::new(Inst::ExtractField {
                        ty: agg_tys[i + 1].clone(),
                        aggregate: aggs[i],
                        field: chain[i].1,
                    })
                    .with_result(sub),
                );
                aggs.push(sub);
            }
            // Extract the leaf scalar, apply the checked binop, then re-insert the result UP the chain.
            let cur = self.fresh();
            self.push_node(InstrNode::new(Inst::ExtractField {
                    ty: ty.clone(),
                    aggregate: aggs[chain.len() - 1],
                    field: chain[chain.len() - 1].1,
                })
                .with_result(cur),
            );
            let result =
                self.emit_arith_binop(span, bin_op, ty.clone(), signed, rhs_rty, cur, r)?;
            let mut newval = result;
            for i in (0..chain.len()).rev() {
                let next = self.fresh();
                self.push_node(InstrNode::new(Inst::InsertField {
                        ty: agg_tys[i].clone(),
                        aggregate: aggs[i],
                        field: chain[i].1,
                        value: newval,
                    })
                    .with_result(next),
                );
                newval = next;
            }
            self.push_node(InstrNode::new(Inst::Store {
                ty: struct_ty,
                ptr,
                value: newval,
                volatile: false,
                align: None,
            }));
            return None;
        }

        // Bare-local (or promoted-local) form.
        let var = match self.place_local(lhs) {
            Some(v) => v,
            None => {
                // `a.b += e` / `a[i] += e` — a projected place we do not version yet.
                self.unsupported.push((format!("{span:?}"), "AssignOp(non-local place)"));
                return None;
            }
        };
        // RHS first (MIR order: `as_local_operand(rhs)` precedes the place read), so a use of the
        // local INSIDE the rhs — or an rhs that reassigns it — is observed before the read.
        let r = match self.lower_expr(rhs) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "AssignOp(rhs no value)"));
                return None;
            }
        };
        if self.is_borrow_ptr(r) {
            self.unsupported.push((format!("{span:?}"), "AssignOp(borrow ptr rhs)"));
            return None;
        }
        if self.is_promoted(var) {
            // Memory-backed local: Load its slot, compute, Store back — a `&mut` alias observes
            // the write, exactly like the `Assign` arm's promoted path.
            let (slot, slot_ty) = match (self.promoted_slot(var), self.promoted_ty(var)) {
                (Some(s), Some(t)) => (s, t),
                _ => {
                    self.unsupported.push((format!("{span:?}"), "AssignOp(promoted slot missing)"));
                    return None;
                }
            };
            let cur = self.fresh();
            self.push_node(InstrNode::new(Inst::Load {
                    ty: slot_ty.clone(),
                    ptr: slot,
                    volatile: false,
                    align: None,
                })
                .with_result(cur),
            );
            let result =
                self.emit_arith_binop(span, bin_op, slot_ty.clone(), signed, rhs_rty, cur, r)?;
            self.push_node(InstrNode::new(Inst::Store {
                ty: slot_ty,
                ptr: slot,
                value: result,
                volatile: false,
                align: None,
            }));
            return None;
        }
        // SSA local: read the current version, compute, rebind (the same last-write-wins rebind a
        // plain `y = …` uses, so the if/match/loop merges carry it automatically).
        let cur = match self.local_value(var) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "AssignOp(unbound local)"));
                return None;
            }
        };
        if self.is_borrow_ptr(cur) {
            self.unsupported.push((format!("{span:?}"), "AssignOp(borrow ptr lhs)"));
            return None;
        }
        let result = self.emit_arith_binop(span, bin_op, ty.clone(), signed, rhs_rty, cur, r)?;
        self.set_local(var, result, ty);
        None
    }

    /// Trust: evaluate a named/inline constant `(def_id, args)` — `ExprKind::NamedConst` (`i32::MAX`,
    /// a user `const` item, an associated const) or `ExprKind::ConstBlock` (`const { … }`) — to a
    /// SCALAR `Inst::Const`. Resolution + evaluation go through `const_eval_resolve_for_typeck`,
    /// the same valtree query pattern-matching uses (cycle-safe inside `mir_built`: rustc itself
    /// evaluates pattern inline constants while building the parent's MIR — see the "Don't steal
    /// here" comment in builder/mod.rs). Only integer/bool results are admitted; the raw bits are
    /// reinterpreted in the expression's width/signedness via the same `sign_extend` the
    /// literal-pattern path uses, so `i8`-MIN etc. carry the correct negative `i128`.
    ///
    /// LOCAL consts are NOT evaluated here (reentrancy — see the deferral arm below): a scalar
    /// local const whose use-site args are all-region emits a PLACEHOLDER
    /// `Inst::Const { ty, value: Constant::PhantomData }` plus a [`PendingConst`] side-table
    /// entry, and the `crate_module` finalizer evaluates + patches it at the reentrancy-safe
    /// `analysis` seam. The placeholder value is NEVER interpreted (both differentials skip
    /// pending-const bodies) and NEVER reaches an artifact unpatched (finalizer tripwire).
    ///
    /// FAIL-CLOSED (each with the caller's precise tag):
    ///   * `non_scalar_tag` — the const's type is not an int/bool (float/char/aggregate/&str/…),
    ///     or its width does not map;
    ///   * `eval_failed_tag` — still-generic args (`T::MAX` in a generic body; the query cannot
    ///     resolve them and `bug!`s on inference vars, so we check first), a reported const-eval
    ///     error, or a non-leaf valtree;
    ///   * `local_deferred_tag` — a const defined in THIS crate whose use-site args carry a
    ///     NON-REGION component (e.g. `Foo::<u8>::C` — concrete, but a `GenericArgsRef` is
    ///     tcx-interned and cannot be carried to the finalizer, and identity-args re-derivation
    ///     is only lossless for region args). Evaluating it from inside `mir_built` would
    ///     re-enter this crate's MIR building (E0391 cycles, a CTFE type-const ICE, or a
    ///     silently swallowed hook tail), so it stays fail-closed.
    /// Trust (wave-CP): lower a const-generic parameter READ to a value-less symbolic global
    /// (`GlobalAddr` + `Load`). See the call site for the rationale; the body is marked SYMBOLIC
    /// by the existing `symbolic_consts` bookkeeping, so it is excluded from the interpretation
    /// differential and the crate splice at their own seams.
    fn lower_const_param(
        &mut self,
        span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
    ) -> Option<ValueId> {
        // Scalar-typed const params only. A const param whose TYPE is itself generic, or of a
        // composite type, has no trust-ir scalar spelling — decline with a precise tag.
        let ty = self.map_ty(expr_ty);
        let scalar = matches!(expr_ty.kind(), ty::Bool)
            || (matches!(expr_ty.kind(), ty::Int(_) | ty::Uint(_) | ty::Char)
                && int_scalar_bits(&ty).is_some());
        if !scalar {
            self.unsupported.push((format!("{span:?}"), "ConstParam(non-scalar type)"));
            return None;
        }
        // Reuse the symbolic ledger keyed by (def_id, empty args): a const PARAM is identified by
        // its own DefId alone, and sharing the ledger keeps ONE symbolic-body rule for both
        // lanes (`Lowered::symbolic` is `!symbolic_consts.is_empty()`).
        let args = ty::List::empty();
        let global = match self.symbolic_consts.iter().find(|(d, a, _)| *d == def_id && a.is_empty())
        {
            Some((_, _, g)) => *g,
            None => {
                let idx = self.pending_globals.len();
                let name = rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "__trust_constparam_{idx}__{}",
                    self.tcx.def_path_str(def_id)
                ));
                self.pending_globals.push(Global {
                    name,
                    ty: ty.clone(),
                    mutable: false,
                    initializer: None,
                    linkage: Linkage::External,
                    tls: None,
                    align: None,
                });
                let g = GlobalId::new(idx as u32);
                self.symbolic_consts.push((def_id, args, g));
                g
            }
        };
        let ptr = self.fresh();
        self.cur.push(InstrNode::new(Inst::GlobalAddr { global }).with_result(ptr));
        let res = self.fresh();
        self.cur.push(
            InstrNode::new(Inst::Load { ty, ptr, volatile: false, align: None }).with_result(res),
        );
        Some(res)
    }

    /// Trust (wave-SR2): lower a `static` READ's address to `Inst::GlobalAddr` over a body-scoped
    /// immutable global holding the static's const-evaluated initializer. See the call site for
    /// the full fail-closed rationale. Returns the `Ty::Ptr` address value, or `None` (with a
    /// precise tag pushed) on any decline.
    fn lower_static_ref(
        &mut self,
        span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
    ) -> Option<ValueId> {
        let tcx = self.tcx;
        // Defense in depth: this arm may only ever see a `static` item.
        if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Static { .. }) {
            self.unsupported.push((format!("{span:?}"), "StaticRef(non-static def)"));
            return None;
        }
        // FOREIGN statics (`extern "C" { static C: u8; }`) have NO initializer body — asking for
        // one ICEs in typeck ("can't type-check body of DefId(… {extern#0}::C)"). Their value is
        // supplied by another object at link time and is not knowable here at all. Decline.
        // (Learned the hard way: this gate was in the plan, omitted from the first
        // implementation, and the corpus burn-in caught it as 2 flag_induced_ice.)
        if tcx.is_foreign_item(def_id) {
            self.unsupported.push((format!("{span:?}"), "StaticRef(foreign static)"));
            return None;
        }
        // `static mut` / `#[thread_local]`: an immutable global cannot stand for either.
        if tcx.is_mutable_static(def_id) {
            self.unsupported.push((format!("{span:?}"), "StaticRef(mutable static)"));
            return None;
        }
        if tcx.is_thread_local_static(def_id) {
            self.unsupported.push((format!("{span:?}"), "StaticRef(thread-local)"));
            return None;
        }
        // LOCAL statics are admitted here (unlike local CONSTS): `lower_named_const`'s E0391
        // hazard is specific to inline/anon consts, which are CHILDREN of the body being built.
        // A `static` is a module-level ITEM whose initializer body cannot reference the function
        // being lowered. The read below uses `eval_static_initializer`, which is the query
        // designed for statics — NOT `const_eval_poly`, which asserts against statics outright
        // ("statics are conceptually places, not values -- so what we do here could break
        // pointer identity", rustc_const_eval eval_queries.rs). An eval error declines below.
        // The STATIC's own type is the pointee of this expression's `*const T`/`&T` type.
        let pointee = match expr_ty.kind() {
            ty::RawPtr(inner, _) => *inner,
            ty::Ref(_, inner, _) => *inner,
            _ => {
                self.unsupported.push((format!("{span:?}"), "StaticRef(non-pointer ty)"));
                return None;
            }
        };
        // Interior mutability: a non-`Freeze` static's value is not fixed, so an immutable
        // global would license folding a value that changes underneath.
        if !pointee.is_freeze(tcx, ty::TypingEnv::fully_monomorphized()) {
            self.unsupported.push((format!("{span:?}"), "StaticRef(interior mutable)"));
            return None;
        }
        // One global per static: repeated reads must Load the SAME id.
        if let Some((_, g)) = self.static_globals.iter().find(|(d, _)| *d == def_id) {
            let g = *g;
            let ptr = self.fresh();
            self.cur.push(InstrNode::new(Inst::GlobalAddr { global: g }).with_result(ptr));
            self.borrow_ptrs.push(ptr);
            self.global_ptrs.push(ptr);
            return Some(ptr);
        }
        // Const-evaluate the initializer through the SAME scalar decoder the non-local const
        // lane uses — no separate value path, so the admitted set can never drift.
        let (gty, init) = match self.eval_nonlocal_static_scalar(span, pointee, def_id) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "StaticRef(initializer not scalar)"));
                return None;
            }
        };
        let idx = self.pending_globals.len();
        let name = rustc_middle::ty::print::with_no_trimmed_paths!(format!(
            "__trust_static_{idx}__{}",
            tcx.def_path_str(def_id)
        ));
        self.pending_globals.push(Global {
            name,
            ty: gty,
            mutable: false,
            initializer: Some(init),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        let global = GlobalId::new(idx as u32);
        self.static_globals.push((def_id, global));
        let ptr = self.fresh();
        self.cur.push(InstrNode::new(Inst::GlobalAddr { global }).with_result(ptr));
        // Same registration as the wave-16 promoted lane: the address is `'static`, so the
        // return-escape guards ADMIT returning it while every other borrow-ptr escape guard
        // still fails closed on it.
        self.borrow_ptrs.push(ptr);
        self.global_ptrs.push(ptr);
        Some(ptr)
    }

    fn lower_named_const(
        &mut self,
        span: rustc_span::Span,
        rty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
        args: ty::GenericArgsRef<'tcx>,
        non_scalar_tag: &'static str,
        eval_failed_tag: &'static str,
        local_deferred_tag: &'static str,
    ) -> Option<ValueId> {
        // Scalar-type gate FIRST, so a non-scalar const gets the precise non-scalar tag.
        // Trust (wave-8b): FLOAT consts (`f32`/`f64`) join the scalar fragment — a named/assoc
        // const of float type (`f32::NAN`, `const X: f32 = …`) evaluates to an IEEE-754 value the
        // producer already models (`Ty::F32`/`F64` + `Constant::Float`, wave 3). f16/f128 fall to
        // the `_` non-scalar arm (their `map_ty` is unsupported anyway). Floats never flip (the
        // shim's `const_of` fails closed on a non-int/bool value) — this is a clean-rate lever.
        let (signed, is_bool, is_float) = match rty.kind() {
            ty::Int(_) => (true, false, false),
            ty::Uint(_) => (false, false, false),
            ty::Bool => (false, true, false),
            ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => (false, false, true),
            // Trust (wave-CH/B1): a `char` const joins the unsigned integer-shaped value fragment
            // while retaining first-class `Ty::Char`. `try_to_bits` accepts a `Char` valtree,
            // `int_scalar_bits(Char) = (32, false)`, and `sign_extend(cp, false, 32)` preserves the
            // code point. The faithful MIR oracle also retains `Char`, so type identity and value
            // bits agree. A char body FLIPPING is comparator-gated; this arm only removes the
            // fail-closed `non_scalar_tag`, it never fabricates a value.
            ty::Char => (false, false, false),
            // Trust (B7, RFC TRUST_IR_V2 Phase 3): COMPOSITE consts (tuple/array/
            // struct/enum) take their own eager path — CTFE branch valtree ->
            // recursive `Constant::Aggregate` decode. Everything else keeps the
            // fail-closed non-scalar tag inside the composite path's own gate.
            ty::Tuple(_) | ty::Array(..) | ty::Adt(..) => {
                return self.lower_composite_named_const(
                    span,
                    rty,
                    def_id,
                    args,
                    non_scalar_tag,
                    eval_failed_tag,
                    local_deferred_tag,
                );
            }
            _ => {
                self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                return None;
            }
        };
        // Inference-dependent args are compiler artifacts, never semantic — fail closed.
        // (Batch C split: the PARAM case is handled below, after the scalar/width mapping,
        // by the symbolic-constant arm instead of failing closed.)
        if args.has_non_region_infer() {
            self.unsupported.push((format!("{span:?}"), eval_failed_tag));
            return None;
        }
        // Trust: mapped trust-ir type + width, shared by the eager (non-local) and deferred
        // (local placeholder) paths. Computed BEFORE the locality split so the placeholder
        // `Inst::Const` carries the same `ty` an eager lowering would, and the finalizer's
        // patch only ever swaps the sentinel `value`. `map_ty` on the scalar-gated Int/Uint is
        // total on this tree's widths (isize/usize resolve via the target pointer size), but
        // the `int_scalar_bits` guard stays — fail-closed over assumed.
        // Trust (wave-8b): for a float const, `bits` is the IEEE width (32/64) — it is NOT a
        // `sign_extend` width but the finalizer's f32-vs-f64 discriminator, and the shape tripwire's
        // width cross-check (`eval_pending_const`). `map_ty` on the F32/F64-gated `rty` is total.
        let (ty, bits) = if is_bool {
            (Ty::Bool, 1u32)
        } else if is_float {
            match self.map_ty(rty) {
                t @ Ty::F32 => (t, 32u32),
                t @ Ty::F64 => (t, 64u32),
                _ => {
                    self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                    return None;
                }
            }
        } else {
            let ty = self.map_ty(rty);
            match int_scalar_bits(&ty) {
                Some((b, _)) => (ty, b),
                None => {
                    self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                    return None;
                }
            }
        };
        // Trust (totality Batch C): a LIVE GENERIC PARAM in the args (`B::BOOL` /
        // `U::USIZE` inside a generic body — typenum's entire assoc-const vocabulary)
        // has NO value until monomorphization; evaluation here is impossible in
        // principle, and this arm must run BEFORE the wave-CC resolution below (whose
        // `TypingEnv::fully_monomorphized()` is only legal for param-free args).
        // Previously fail-closed. Now: model the read as `GlobalAddr` + `Load` of a
        // body-scoped EXTERN IMMUTABLE global — trust-ir's native "declared, value
        // unknown" vocabulary (`initializer: None`, `Linkage::External`) — deduped per
        // `(def_id, args)` so repeated reads Load the SAME immutable global and
        // read-read equality is structural. The body becomes SYMBOLIC
        // (`Lowered::symbolic`): it lowers for COVERAGE but is excluded from the
        // interpretation differential and the crate-module splice at their seams (a
        // value-less load must never be interpreted or shipped in the executable
        // module). Param-TYPED consts never reach here (the scalar gate above already
        // failed them closed); only the VALUE is symbolic, the type is concrete.
        if args.has_non_region_param() {
            let global =
                match self.symbolic_consts.iter().find(|(d, a, _)| *d == def_id && *a == args) {
                    Some((_, _, g)) => *g,
                    None => {
                        let idx = self.pending_globals.len();
                        let name = rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                            "__trust_symconst_{idx}__{}",
                            self.tcx.def_path_str_with_args(def_id, args)
                        ));
                        self.pending_globals.push(Global {
                            name,
                            ty: ty.clone(),
                            mutable: false,
                            initializer: None,
                            linkage: Linkage::External,
                            tls: None,
                            align: None,
                        });
                        let g = GlobalId::new(idx as u32);
                        self.symbolic_consts.push((def_id, args, g));
                        g
                    }
                };
            let ptr = self.fresh();
            self.push_node(InstrNode::new(Inst::GlobalAddr { global }).with_result(ptr));
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::Load { ty, ptr, volatile: false, align: None })
                    .with_result(res),
            );
            return Some(res);
        }
        // Trust: a LOCAL const's value can require building THIS crate's MIR — an inline
        // `const {}` / anonymous const interleaves its `mir_built` with the parent body being
        // built right now, so evaluating it from inside this hook re-enters the query stack:
        // observed as E0391 "cycle detected when building MIR" on inline-const/offset_of
        // bodies, a CTFE type-const ICE (mgca), and — worst — a swallowed hook tail that
        // silently drops the parent body's differential/registry events. Non-local consts
        // (`i32::MAX`, upstream `const` items) are already evaluated in metadata and cannot
        // recurse here.
        //
        // DEFERRAL (reentrancy-safe local-const eval): instead of failing closed, emit a
        // placeholder `Inst::Const { ty, value: Constant::PhantomData }` (the structurally
        // unmistakable sentinel — see [`PendingConst`]) and record a side-table entry; the
        // `crate_module` finalizer evaluates the const at the `rustc_interface` `analysis`
        // seam (all MIR already built there — `run_required_analyses` has forced
        // `mir_borrowck`, hence `mir_built`, for every body owner, so
        // `const_eval_resolve_for_typeck` cannot re-enter an in-flight query) and patches the
        // real value in before dump. Only taken when the use-site args are ALL-REGION: the
        // finalizer re-derives them losslessly via `identity_for_item` + region erasure (a
        // region never affects a const's value). Anything else (`Foo::<u8>::C` — concrete
        // non-region args we cannot store across the hook/finalizer boundary) keeps the
        // fail-closed deferred tag. An mgca `type const` (the observed CTFE ICE class —
        // tests/ui/const-generics/mgca/type_const-use.rs; the ICE is in the type-const CTFE
        // path itself, not just the reentrancy) also keeps the fail-closed tag: it must never
        // reach the finalizer's evaluation either.
        // Trust (wave-CC): RESOLVE an assoc const to its concrete impl-const item BEFORE the
        // locality split. A LOCAL concrete associated const — `<i32 as Foo>::ID` — has USE-SITE
        // args `[i32]` (a non-region Self), so the identity-args deferral below cannot carry it and
        // it would fail closed. But `Instance::resolve` maps it to its `impl Foo for i32 { const ID
        // }` item, whose IDENTITY args are REGION-ONLY (a non-generic impl) → deferrable: the
        // finalizer re-derives them via `identity_for_item` and evals the SAME value. Judge locality
        // + args on the RESOLVED item so this also routes a resolve-to-UPSTREAM assoc const to the
        // eager path below with the right def. Only attempted for a NON-region-args const (the
        // currently-failing case) so region-only item consts (the common path) are untouched; a
        // generic-impl assoc const (`<Vec<T> as Foo>::ID` → resolved args `[T-conc]` still
        // non-region) or an unresolvable/shim const keeps `(def_id, args)` and stays fail-closed.
        // Resolution is a trait query (NOT MIR building), so no new reentrancy — the deferred value
        // is still evaluated at the reentrancy-safe `analysis` seam.
        let (def_id, args) = if args.iter().all(|a| a.as_region().is_some()) {
            (def_id, args)
        } else {
            match ty::Instance::try_resolve(
                self.tcx,
                ty::TypingEnv::fully_monomorphized(),
                def_id,
                args,
            ) {
                Ok(Some(inst)) => match inst.def {
                    ty::InstanceKind::Item(d) => (d, inst.args),
                    _ => (def_id, args),
                },
                _ => (def_id, args),
            }
        };
        if def_id.is_local() {
            if !self.tcx.is_type_const(def_id) && args.iter().all(|a| a.as_region().is_some()) {
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::Const { ty, value: Constant::PhantomData })
                        .with_result(res),
                );
                self.pending_consts.push(PendingConst {
                    value: res,
                    def_id,
                    span,
                    is_bool,
                    is_float,
                    signed,
                    bits,
                    composite: false,
                });
                return Some(res);
            }
            self.unsupported.push((format!("{span:?}"), local_deferred_tag));
            return None;
        }
        // Trust: rust 1.99 removed `ty::UnevaluatedConst` — the ty-level unevaluated const is
        // now `ty::AliasConst` (kind classified from the DefId), which is exactly what
        // `const_eval_resolve_for_typeck` takes. Same def/args payload, same erase-then-eval flow.
        let uv = ty::AliasConst::new(
            self.tcx,
            ty::AliasConstKind::new_from_def_id(self.tcx, def_id),
            args,
        );
        let uv = self.tcx.erase_and_anonymize_regions(uv);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let valtree = match self.tcx.const_eval_resolve_for_typeck(typing_env, uv, span) {
            Ok(Ok(v)) => v,
            // `Ok(Err(_))` (a non-valtree'able type) and `Err(_)` (reported error / too generic)
            // both fail closed — never a guessed value.
            _ => {
                self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                return None;
            }
        };
        let value = ty::Value { ty: rty, valtree };
        if is_bool {
            let b = match value.try_to_bool() {
                Some(b) => b,
                None => {
                    self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                    return None;
                }
            };
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(b) })
                    .with_result(res),
            );
            return Some(res);
        }
        // Trust (wave-8b): a float const → `Constant::Float(f64)`, the IEEE bits reinterpreted into
        // the same f64 carrier the float-LITERAL arm uses (`f64::from(f32)` for F32; `from_bits`
        // for F64). `try_to_bits` returns the raw IEEE pattern for a Float valtree (it gates on
        // Bool|Char|Uint|Int|Float). FAITHFULNESS GUARD (unlike a literal, a const can spell a
        // signaling / non-canonical f32 NaN via `f32::from_bits`): the runtime `f32 as f64`
        // widening QUIETS a signaling f32 NaN (verified on host: 0x7fa00000 → carrier → back
        // 0x7fe00000), so the f64 carrier cannot faithfully hold every f32 bit pattern. Require
        // the carrier to round-trip the source bits EXACTLY, else fail closed — never emit a value
        // whose bits differ from the const's true value (the trust-cg object path materializes it).
        // Every finite/±0/±inf/subnormal/canonical-qNaN f32 round-trips, so the ordinary-float-const
        // clean-rate win is preserved; only the exotic un-round-trippable NaN sub-space declines.
        // Fail-closed if the width is not 32/64 (excluded by the type gate, but never assumed).
        if is_float {
            let raw = match value.try_to_bits(self.tcx, typing_env) {
                Some(r) => r,
                None => {
                    self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                    return None;
                }
            };
            let v: f64 = match bits {
                32 => {
                    let carrier = f64::from(f32::from_bits(raw as u32));
                    if (carrier as f32).to_bits() != raw as u32 {
                        self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                        return None;
                    }
                    carrier
                }
                64 => {
                    // `from_bits`/`to_bits` are exact bitcasts for every f64 pattern (incl.
                    // signaling NaN), so this guard is a defensive no-op — kept for symmetry.
                    let carrier = f64::from_bits(raw as u64);
                    if carrier.to_bits() != raw as u64 {
                        self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                        return None;
                    }
                    carrier
                }
                _ => {
                    self.unsupported.push((format!("{span:?}"), non_scalar_tag));
                    return None;
                }
            };
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty, value: Constant::Float(v) }).with_result(res),
            );
            return Some(res);
        }
        // `ty`/`bits` were mapped + guarded above (shared with the deferral path).
        let raw = match value.try_to_bits(self.tcx, typing_env) {
            Some(r) => r,
            None => {
                self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                return None;
            }
        };
        let value = integer_constant_from_bits(raw, signed, bits);
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty, value }).with_result(res));
        Some(res)
    }

    /// Trust (B7, RFC TRUST_IR_V2 Phase 3): the COMPOSITE leg of [`Self::lower_named_const`] —
    /// a named/assoc const of tuple/array/struct/enum type evaluates through CTFE to a BRANCH
    /// valtree and decodes recursively into the producer's aggregate constant model
    /// (`Constant::Aggregate` under the `map_ty` spelling; enums as the `[Int(discriminant),
    /// fields...]` tag+payload convention the interpreter's `constant_to_value` executes and
    /// wave-ES seeds share). NON-LOCAL only: the deferral pair (`PendingConst` +
    /// `eval_pending_const`) carries a SCALAR-ONLY shape record, and per the paired-gate lesson
    /// this slice never emits a composite sentinel — a LOCAL composite const keeps the
    /// fail-closed `local_deferred_tag` (no leak channel exists by construction). Fail-closed
    /// everywhere else: a shape the decoder cannot prove faithful keeps its tag, never a
    /// guessed value.
    fn lower_composite_named_const(
        &mut self,
        span: rustc_span::Span,
        rty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
        args: ty::GenericArgsRef<'tcx>,
        non_scalar_tag: &'static str,
        eval_failed_tag: &'static str,
        local_deferred_tag: &'static str,
    ) -> Option<ValueId> {
        if args.has_non_region_param() || args.has_non_region_infer() {
            self.unsupported.push((format!("{span:?}"), eval_failed_tag));
            return None;
        }
        // The emitted `Inst::Const` type IS the map_ty spelling (registering the
        // struct/enum defs as a side effect). KIND-COHERENCE GATE: admission must only
        // accept (and, for locals, only DEFER) pairings the decoders provably handle —
        // the rustc kind and the mapped spelling are matched PAIRWISE, not independently.
        // An enum const is admitted only when `map_ty` produced first-class
        // `Ty::Enum`; an opaque/declined enum cannot leak a PendingConst sentinel.
        let ty = self.map_ty(rty);
        let coherent = match (rty.kind(), &ty) {
            (ty::Tuple(_), Ty::Tuple(_)) => true,
            (ty::Array(..), Ty::Tuple(_) | Ty::Array(_, 0)) => true,
            (ty::Adt(adt, _), Ty::Struct(_)) if adt.is_struct() => true,
            (ty::Adt(adt, _), Ty::Enum(_)) if adt.is_enum() => true,
            _ => false,
        };
        if !coherent {
            self.unsupported.push((format!("{span:?}"), non_scalar_tag));
            return None;
        }
        // Wave-CC assoc-const resolution, verbatim from the scalar leg: judge locality on
        // the RESOLVED item so `<T as Tr>::C` routes to its concrete impl const.
        let (def_id, args) = if args.iter().all(|a| a.as_region().is_some()) {
            (def_id, args)
        } else {
            match ty::Instance::try_resolve(
                self.tcx,
                ty::TypingEnv::fully_monomorphized(),
                def_id,
                args,
            ) {
                Ok(Some(inst)) => match inst.def {
                    ty::InstanceKind::Item(d) => (d, inst.args),
                    _ => (def_id, args),
                },
                _ => (def_id, args),
            }
        };
        if def_id.is_local() {
            // Same reentrancy-safe deferral as the scalar leg (evaluating a LOCAL const here
            // can re-enter `mir_built`): emit the PhantomData sentinel under the mapped
            // composite `ty` and record `composite: true` — the finalizer's composite leg
            // decodes the branch valtree against this node's `ty` + the body's registered
            // struct/enum tables. Same all-region/mgca gates as the scalar leg.
            if !self.tcx.is_type_const(def_id) && args.iter().all(|a| a.as_region().is_some()) {
                let res = self.fresh();
                self.push_node(InstrNode::new(Inst::Const { ty, value: Constant::PhantomData })
                        .with_result(res),
                );
                self.pending_consts.push(PendingConst {
                    value: res,
                    def_id,
                    span,
                    is_bool: false,
                    is_float: false,
                    signed: false,
                    bits: 0,
                    composite: true,
                });
                return Some(res);
            }
            self.unsupported.push((format!("{span:?}"), local_deferred_tag));
            return None;
        }
        let uv = ty::AliasConst::new(
            self.tcx,
            ty::AliasConstKind::new_from_def_id(self.tcx, def_id),
            args,
        );
        let uv = self.tcx.erase_and_anonymize_regions(uv);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let valtree = match self.tcx.const_eval_resolve_for_typeck(typing_env, uv, span) {
            Ok(Ok(v)) => v,
            _ => {
                self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                return None;
            }
        };
        let value = match self.valtree_to_constant(rty, valtree, 0) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), eval_failed_tag));
                return None;
            }
        };
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty, value }).with_result(res));
        Some(res)
    }

    /// Trust (B7): recursive CTFE-valtree -> producer-constant decoder. Mirrors `map_ty`'s
    /// value model EXACTLY, case by case — the emitted constant must satisfy both the trust-ir
    /// validator's shape checks and the pinned interpreter's `constant_to_value` decoding:
    ///   * scalar leaves reuse the scalar const legs' spellings (`integer_constant_from_bits`
    ///     incl. the v24 U128 canonicality, char as an Int code-point leaf with the validator's
    ///     range check, floats behind the f32-carrier round-trip guard);
    ///   * `(A, B)` and `[T; N > 0]` -> `Constant::Aggregate` under the mapped `Ty::Tuple`;
    ///     `[T; 0]` -> the empty `Constant::Array` under `Ty::Array(_, 0)` (wave-FRU L3);
    ///   * `struct` -> `Constant::Aggregate(fields)` in declaration order (the valtree Branch
    ///     order — rustc documents Branch as "the fields of any kind of aggregate ... in order");
    ///   * `enum` -> `Constant::Aggregate([Int(discriminant), fields...])`, the tag+payload
    ///     convention: the Branch's LEADING element is the u32 VARIANT INDEX, translated to the
    ///     variant's effective DISCRIMINANT via the REGISTERED `EnumDef` (single source of truth
    ///     with the Switch and seed lanes — never re-derived).
    /// Every unproven shape (refs, unions, raw ptrs, strs, ty disagreement between a Branch
    /// element and its declared field type, depth blowout) returns `None` -> the caller's
    /// fail-closed tag.
    fn valtree_to_constant(
        &mut self,
        rty: RustcTy<'tcx>,
        valtree: ty::ValTree<'tcx>,
        depth: usize,
    ) -> Option<Constant> {
        if depth > 64 {
            return None;
        }
        let typing_env = ty::TypingEnv::fully_monomorphized();
        match rty.kind() {
            ty::Bool => ty::Value { ty: rty, valtree }.try_to_bool().map(Constant::Bool),
            // Char consts are Int leaves carrying the code point (the trust-ir validator
            // checks the Unicode scalar range at the `Ty::Char` declaration).
            ty::Char => {
                let raw = ty::Value { ty: rty, valtree }.try_to_bits(self.tcx, typing_env)?;
                Some(Constant::Int(raw as i128))
            }
            ty::Int(_) | ty::Uint(_) => {
                let (bits, signed) = int_scalar_bits(&self.map_ty(rty))?;
                let raw = ty::Value { ty: rty, valtree }.try_to_bits(self.tcx, typing_env)?;
                Some(integer_constant_from_bits(raw, signed, bits))
            }
            // Floats: same f64-carrier + f32 round-trip faithfulness guard as the scalar leg.
            ty::Float(ty::FloatTy::F32) => {
                let raw = ty::Value { ty: rty, valtree }.try_to_bits(self.tcx, typing_env)?;
                let carrier = f64::from(f32::from_bits(raw as u32));
                if (carrier as f32).to_bits() != raw as u32 {
                    return None;
                }
                Some(Constant::Float(carrier))
            }
            ty::Float(ty::FloatTy::F64) => {
                let raw = ty::Value { ty: rty, valtree }.try_to_bits(self.tcx, typing_env)?;
                Some(Constant::Float(f64::from_bits(raw as u64)))
            }
            ty::Tuple(fields) => {
                let branch = valtree.try_to_branch()?;
                if branch.len() != fields.len() {
                    return None;
                }
                branch
                    .iter()
                    .zip(fields.iter())
                    .map(|(c, fty)| self.branch_elem_to_constant(c, fty, depth + 1))
                    .collect::<Option<Vec<_>>>()
                    .map(Constant::Aggregate)
            }
            ty::Array(elem_ty, _) => {
                let branch = valtree.try_to_branch()?;
                let elems = branch
                    .iter()
                    .map(|c| self.branch_elem_to_constant(c, *elem_ty, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                // map_ty's array model: `[T; N > 0]` is a Ty::Tuple (Aggregate value);
                // `[T; 0]` is the ZST Ty::Array (empty Array value, wave-FRU L3).
                if elems.is_empty() {
                    Some(Constant::Array(Vec::new()))
                } else {
                    Some(Constant::Aggregate(elems))
                }
            }
            ty::Adt(adt, adt_args) if adt.is_struct() => {
                let branch = valtree.try_to_branch()?;
                let variant = adt.non_enum_variant();
                if branch.len() != variant.fields.len() {
                    return None;
                }
                branch
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(c, f)| {
                        self.branch_elem_to_constant(
                            c,
                            f.ty(self.tcx, adt_args).skip_normalization(),
                            depth + 1,
                        )
                    })
                    .collect::<Option<Vec<_>>>()
                    .map(Constant::Aggregate)
            }
            ty::Adt(adt, adt_args) if adt.is_enum() => {
                // Branch = [variant-index-leaf(u32), selected variant's fields...].
                let branch = valtree.try_to_branch()?;
                let (vt_idx, field_consts) = branch.split_first()?;
                let ty::ConstKind::Value(iv) = vt_idx.kind() else { return None };
                let vidx = usize::try_from(iv.try_to_bits(self.tcx, typing_env)?).ok()?;
                // The discriminant comes from the REGISTERED EnumDef (its admission gate
                // already proved every variant seedable + the tag lane canonical) — the
                // exact value the Switch lane and the variant-0 seed carry.
                let Ty::Enum(eid) = self.map_ty(rty) else { return None };
                let disc = self.registered_enum(eid)?.discriminants.get(vidx).copied().flatten()?;
                let variant = adt.variant(rustc_abi::VariantIdx::from_usize(vidx));
                if field_consts.len() != variant.fields.len() {
                    return None;
                }
                let mut out = Vec::with_capacity(1 + field_consts.len());
                out.push(Constant::Int(disc));
                for (c, f) in field_consts.iter().copied().zip(variant.fields.iter()) {
                    let f_rty = f.ty(self.tcx, adt_args).skip_normalization();
                    // Trust (B3-2c E5): a drop-free-ZST field decodes as the
                    // CANONICAL PhantomData — the admission invariant spelled the
                    // def field Ty::Unit, and the interpreter has no
                    // (Ty::Unit, Aggregate([])) pair (a fmt::Result const would
                    // trap at interpretation = a manufactured divergence). The
                    // finalizer twin carries the same arm (paired-gate rule).
                    if self.is_drop_free_zst(f_rty) {
                        out.push(Constant::PhantomData);
                        continue;
                    }
                    out.push(self.branch_elem_to_constant(c, f_rty, depth + 1)?);
                }
                Some(Constant::Aggregate(out))
            }
            _ => None,
        }
    }

    /// Trust (B7): decode ONE valtree-Branch element (`ty::Const`) against its declared field/
    /// element type. Branch elements are always `ConstKind::Value` for a CTFE-produced valtree;
    /// the recorded type must EQUAL the declared type (a disagreement is a decoder
    /// misunderstanding of rustc's model — fail closed, never coerce).
    fn branch_elem_to_constant(
        &mut self,
        c: ty::Const<'tcx>,
        expected_rty: RustcTy<'tcx>,
        depth: usize,
    ) -> Option<Constant> {
        let ty::ConstKind::Value(v) = c.kind() else { return None };
        if v.ty != expected_rty {
            return None;
        }
        self.valtree_to_constant(v.ty, v.valtree, depth)
    }

    /// Trust (wave-16): try to const-eval the POINTEE sub-expression `arg` of a rustc-PROMOTED
    /// shared `&'static` borrow to a `(trust_ir::Ty, Constant)` WITHOUT emitting any instruction —
    /// the value a module GLOBAL's initializer carries for the promoted-borrow lowering
    /// (`fn f()->&'static i32 { &5 }`, `&C`, `&123u8`, `&true`, `&1.5f32`). Trust (wave-PA)
    /// extends this via `eval_promotable_const_value` to AGGREGATE literals of promotable leaves
    /// (`&[13, 14]`, `&(1u8, true)`, `&S { a: 1, b: 2 }` → a `Constant::Aggregate`). Returns
    /// `None` (caller keeps the fail-closed `Borrow(non-local place)` tag) for EVERYTHING that is
    /// not a scalar int/bool/char/float LITERAL, a NON-LOCAL scalar CONST, or such an aggregate:
    ///   * `&param.field` / `&param[i]` — an `ExprKind::Field`/`Index`, not a literal/const → the
    ///     `_` arm declines (the CRITICAL safety case: a borrow of CALLER data is NON-`'static`
    ///     and must never be promoted to a fresh scalar);
    ///   * `&"s"` / `&&T` — a `LitKind::Str`/`ByteStr` literal, or a reference-typed pointee, is not
    ///     an admitted scalar → declines;
    ///   * `&STATIC` — a `static`'s address is `ExprKind::StaticRef` (never `NamedConst`), so it
    ///     never reaches the const arm; a `static` is never const-eval'd to a fresh scalar (and
    ///     interior mutability must not be promoted);
    ///   * a LOCAL const — `eval_nonlocal_scalar_const` fails it closed (eager local-const eval in
    ///     `mir_built` risks the E0391/CTFE re-entrancy `lower_named_const` defers around, and
    ///     there is no global-initializer patch seam here — a missed clean-rate, never a
    ///     miscompile);
    ///   * generic/inference-dependent args, `f16`/`f128`, an aggregate with a ref/fat/`&str`/
    ///     Call-constructed/non-`Freeze` field (`eval_promotable_const_value` declines it), and
    ///     every other shape.
    ///
    /// Faithfulness: the emitted global holds exactly the value rustc would promote, so `Deref`ing
    /// / returning the address observes the same value. No side effects on decline.
    fn eval_promotable_scalar(&mut self, arg: ExprId) -> Option<(Ty, Constant)> {
        // Peel value-preserving `Scope`/`Use` wrappers to reach the constant-ish core (the same
        // peel every place-shaped arm in this file uses).
        let mut e = arg;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                // Trust (wave-16): peel the REBORROW adjustment rustc inserts for a promoted
                // `&<const>` in a `-> &'static` / coercion position. A direct tail-return `&5`
                // is THIR `Borrow(Deref(Borrow(Literal)))`, so this helper's `arg` is
                // `Deref{Borrow{Literal}}` — `reborrow_target` collapses the same
                // `Deref{Borrow{place}}` (`*&place == place`) but returns the `NotAPlace` enum
                // without the peeled expr, so we redo the collapse here. A `Deref` whose source
                // is NOT a `Borrow` (a real pointer deref `*p`) does NOT peel — never promotable.
                // The final `place` is still matched by the scalar-only arms below, so a
                // `Deref{Borrow{Field/Index/StaticRef}}` (`&param.field`, `&param[i]`, `&STATIC`)
                // peels to that non-scalar core and correctly FAILS CLOSED.
                ExprKind::Deref { arg: darg } => {
                    let mut inner = *darg;
                    loop {
                        match &self.thir.exprs[inner].kind {
                            ExprKind::Scope { value, .. } => inner = *value,
                            ExprKind::Use { source } => inner = *source,
                            _ => break,
                        }
                    }
                    match &self.thir.exprs[inner].kind {
                        ExprKind::Borrow { arg: place, .. } => e = *place,
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        // Trust (wave-PA): the peeled pointee `e` is a scalar OR an aggregate literal — evaluate it
        // (recursively) to `(pointee Ty, Constant)`. The scalar arms are wave-16; the aggregate arms
        // extend the promoted-borrow path to `&[a, b]` / `&(a, b)` / `&S { .. }` of promotable leaves.
        self.eval_promotable_const_value(e)
    }

    /// Trust (wave-PA): recursively const-eval a PROMOTABLE value expr — a scalar literal/const
    /// (wave-16) OR an aggregate LITERAL (`[a, b]` / `(a, b)` / `S { .. }`) all of whose leaves are
    /// themselves promotable — to `(Ty, Constant)` for a promoted-borrow module global. The mapped
    /// aggregate `Ty` is `map_ty(pointee)` (`[T; N]`/tuple → `Ty::Tuple`, struct → `Ty::Struct`) and
    /// the value a matching `Constant::Aggregate`. CLEAN-ONLY (a promoted-borrow global is never
    /// flipped/interpreted, exactly like the wave-16 scalar path). FAIL CLOSED (`None`) on any
    /// non-promotable shape so an unrepresentable field never mints an ill-typed global: a
    /// ref/fat-ptr/`&str` field (declines as a non-literal — a `Constant` cannot hold a pointer),
    /// a `Cell::new(..)`/other Call-constructed value, `..base`/functional-update, union/enum, a
    /// non-`Freeze` (interior-mutable) aggregate, an arity/`map_ty` mismatch, or a generic type.
    fn eval_promotable_const_value(&mut self, e0: ExprId) -> Option<(Ty, Constant)> {
        // Peel value-preserving wrappers (NOT `Deref{Borrow}` — a field is a direct value, never a
        // borrow-adjustment; a ref-typed field therefore declines below rather than being peeled).
        let mut e = e0;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                _ => break,
            }
        }
        // `ety` is the value's type. Both borrows below read through `self.thir` (a `&'a Thir`), so
        // they do not conflict with the `&mut self` eval calls.
        let ety = self.thir.exprs[e].ty;
        let span = self.thir.exprs[e].span;
        match &self.thir.exprs[e].kind {
            // A scalar literal — reuse the EXACT value mapping the `ExprKind::Literal` emit-arm
            // uses (int width via `map_ty`; char → first-class `Ty::Char`; float parsed into the
            // `f64` carrier),
            // but return `(Ty, Constant)` instead of emitting an `Inst::Const`.
            ExprKind::Literal { lit, neg } => {
                let neg = *neg;
                match lit.node {
                    LitKind::Int(v, _) => {
                        let ty = self.map_ty(ety);
                        // Only a fixed-width int is a scalar the global can carry.
                        let Some((bits, signed)) = int_scalar_bits(&ty) else {
                            return None;
                        };
                        Some((ty, integer_literal_constant(v.get(), neg, signed, bits)))
                    }
                    LitKind::Bool(b) => Some((Ty::Bool, Constant::Bool(b))),
                    LitKind::Char(c) => Some((Ty::Char, Constant::Int(c as u32 as i128))),
                    LitKind::Float(sym, _) => {
                        let ty = self.map_ty(ety);
                        let stripped = sym.as_str().replace('_', "");
                        let v: Option<f64> = match ty {
                            Ty::F32 => stripped
                                .parse::<f32>()
                                .ok()
                                .map(|f| f64::from(if neg { -f } else { f })),
                            Ty::F64 => {
                                stripped.parse::<f64>().ok().map(|f| if neg { -f } else { f })
                            }
                            _ => None,
                        };
                        v.map(|f| (ty, Constant::Float(f)))
                    }
                    // Str / ByteStr / other — not a promotable scalar.
                    _ => None,
                }
            }
            ExprKind::NamedConst { def_id, args, .. } => {
                let def_id = *def_id;
                let args = *args;
                self.eval_nonlocal_scalar_const(span, ety, def_id, args)
            }
            ExprKind::ConstBlock { did, args } => {
                let did = *did;
                let args = *args;
                self.eval_nonlocal_scalar_const(span, ety, did, args)
            }
            // Trust (wave-PA): aggregate literals of promotable values.
            ExprKind::Array { fields } => {
                let fields: Vec<ExprId> = fields.iter().copied().collect();
                self.eval_promotable_aggregate(ety, &fields)
            }
            ExprKind::Tuple { fields } => {
                let fields: Vec<ExprId> = fields.iter().copied().collect();
                self.eval_promotable_aggregate(ety, &fields)
            }
            ExprKind::Adt(adt_expr) => {
                // STRUCT literal only, no `..base` (functional update pulls fields from another
                // value we do not thread here). Enums/unions fail closed — a `Constant::Aggregate`
                // for the general enum model would need the tag+payload shape, out of scope.
                let adt = adt_expr.adt_def;
                if !adt.is_struct()
                    || !matches!(adt_expr.base, rustc_middle::thir::AdtExprBase::None)
                {
                    return None;
                }
                // Fields at their DESTINATION index (`FieldExpr.name`), NOT source-write order —
                // matching `map_ty`/`registered_struct_field_tys` declaration order. A struct
                // literal writes every field, so every slot must be present (else fail closed).
                let n = adt.non_enum_variant().fields.len();
                let mut by_idx: Vec<Option<ExprId>> = vec![None; n];
                for f in adt_expr.fields.iter() {
                    let idx = f.name.as_usize();
                    if idx >= n {
                        return None;
                    }
                    by_idx[idx] = Some(f.expr);
                }
                let fields: Vec<ExprId> = by_idx.into_iter().collect::<Option<Vec<_>>>()?;
                self.eval_promotable_aggregate(ety, &fields)
            }
            _ => None,
        }
    }

    /// Trust (wave-PA): const-eval an aggregate whose `pointee` type maps to a thin in-fragment
    /// `Ty::Tuple`/`Ty::Struct` and whose `fields` (in declaration/mapped order) are all promotable.
    /// Fields are evaluated FIRST — a decline means `map_ty` is never called, so a body that stays
    /// `Borrow(non-local place)` never also picks up a spurious `Ty` gap from a partial map.
    fn eval_promotable_aggregate(
        &mut self,
        pointee: RustcTy<'tcx>,
        fields: &[ExprId],
    ) -> Option<(Ty, Constant)> {
        // FREEZE (defense-in-depth): rustc only promotes `Freeze` borrows; minting a FRESH global
        // for an interior-mutable aggregate would break the shared-identity semantics of a `&Cell`.
        // (Interior-mut types have private fields and cannot be written as an `Adt`/`Array`/`Tuple`
        // LITERAL here anyway — a `Cell::new(..)` is an `ExprKind::Call`, not matched above — so
        // this gate is belt-and-suspenders, never the sole line of defense.)
        let typing_env = ty::TypingEnv::fully_monomorphized();
        if !pointee.is_freeze(self.tcx, typing_env) {
            return None;
        }
        let mut consts = Vec::with_capacity(fields.len());
        for &f in fields {
            let (_fty, c) = self.eval_promotable_const_value(f)?;
            consts.push(c);
        }
        // Every field promotable ⇒ the aggregate is a clean scalar/aggregate value, so `map_ty`
        // maps it without recording a gap. Require a thin `Ty::Tuple`/`Ty::Struct` of matching
        // arity (a fat/ptr/enum/array-0 mapping declines — the `Constant::Aggregate` would not match).
        let agg_ty = self.map_ty(pointee);
        let expected = match &agg_ty {
            Ty::Tuple(elems) => elems.len(),
            Ty::Struct(sid) => self.registered_struct_field_tys(*sid)?.len(),
            _ => return None,
        };
        if expected != consts.len() {
            return None;
        }
        Some((agg_ty, Constant::Aggregate(consts)))
    }

    /// Trust (wave-16): EAGER, non-emitting scalar const-eval for the promoted-borrow path.
    /// Mirrors `lower_named_const`'s scalar gate + eager `const_eval_resolve_for_typeck` +
    /// bit-reinterpretation (incl. the wave-8b float round-trip guard), but returns
    /// `(Ty, Constant)` (no `Inst::Const`, no `unsupported` push) and has NO local-const
    /// deferral — a LOCAL const fails closed (`None`), because a module global's initializer
    /// cannot be a deferred placeholder and eager local-const eval inside `mir_built` risks the
    /// re-entrancy `lower_named_const` documents. Returns `None` on any decline.
    /// Trust (wave-SR2): const-evaluate a NON-LOCAL `static`'s initializer to the same admitted
    /// scalar set `eval_nonlocal_scalar_const` accepts (int / bool / f32 / f64), reusing its
    /// decode so the two lanes can never drift apart. A `static` takes no generic args, so this
    /// is the args-free twin; every other shape declines.
    fn eval_nonlocal_static_scalar(
        &mut self,
        span: rustc_span::Span,
        rty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
    ) -> Option<(Ty, Constant)> {
        // A `static` is a PLACE: its contents live in an allocation, read through
        // `eval_static_initializer` — the query DESIGNED for statics. `const_eval_poly` asserts
        // outright against them ("statics are conceptually places, not values -- so what we do
        // here could break pointer identity", rustc_const_eval/src/const_eval/eval_queries.rs),
        // which this lane learned by ICEing on the first local static it met. Reading the INITIAL
        // contents is faithful only because the caller already established the static is
        // immutable, non-thread-local and `Freeze` — under those gates the initial bytes are the
        // value for all time.
        let _ = span;
        let alloc = self.tcx.eval_static_initializer(def_id).ok()?;
        let inner = alloc.inner();
        let ty = self.map_ty(rty);
        let bits = match rty.kind() {
            ty::Bool => 8u32,
            ty::Int(_) | ty::Uint(_) => int_scalar_bits(&ty)?.0,
            // Floats, pointers, aggregates and str are outside this slice's admitted set.
            _ => return None,
        };
        let size = rustc_abi::Size::from_bits(u64::from(bits));
        // `read_provenance: false` — a scalar static holds plain bytes. A POINTER-valued static
        // reads back with provenance and errors here, which is the correct fail-close: its value
        // is an address this lane does not model.
        let scalar = inner
            .read_scalar(
                &self.tcx,
                rustc_middle::mir::interpret::alloc_range(rustc_abi::Size::ZERO, size),
                false,
            )
            .ok()?;
        let raw = scalar.to_bits(size).discard_err()?;
        match rty.kind() {
            // A `bool` byte that is neither 0 nor 1 is not a value we may invent.
            ty::Bool => match raw {
                0 => Some((Ty::Bool, Constant::Bool(false))),
                1 => Some((Ty::Bool, Constant::Bool(true))),
                _ => None,
            },
            ty::Int(_) | ty::Uint(_) => {
                let signed = matches!(rty.kind(), ty::Int(_));
                // The SAME shared decode the const lane's tail uses — one spelling only.
                Some((ty, integer_constant_from_bits(raw, signed, bits)))
            }
            _ => None,
        }
    }

    fn eval_nonlocal_scalar_const(
        &mut self,
        span: rustc_span::Span,
        rty: RustcTy<'tcx>,
        def_id: rustc_span::def_id::DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Option<(Ty, Constant)> {
        // Defense in depth: only a genuine CONST item — never a `static` (whose address must not
        // be promoted to a fresh scalar). `NamedConst`/`ConstBlock` never name a `static`, but
        // gate anyway so this helper can never CTFE a static's initializer.
        match self.tcx.def_kind(def_id) {
            rustc_hir::def::DefKind::Const { .. }
            | rustc_hir::def::DefKind::AssocConst { .. }
            | rustc_hir::def::DefKind::AnonConst
            | rustc_hir::def::DefKind::InlineConst => {}
            _ => return None,
        }
        // Scalar-type gate (int / bool / f32 / f64 only).
        let (signed, is_bool, is_float) = match rty.kind() {
            ty::Int(_) => (true, false, false),
            ty::Uint(_) => (false, false, false),
            ty::Bool => (false, true, false),
            ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => (false, false, true),
            _ => return None,
        };
        // Generic / inference-dependent args cannot be resolved here.
        if args.has_non_region_param() || args.has_non_region_infer() {
            return None;
        }
        // LOCAL consts: fail closed (no global-initializer deferral; re-entrancy risk).
        if def_id.is_local() {
            return None;
        }
        let (ty, bits) = if is_bool {
            (Ty::Bool, 1u32)
        } else if is_float {
            match self.map_ty(rty) {
                t @ Ty::F32 => (t, 32u32),
                t @ Ty::F64 => (t, 64u32),
                _ => return None,
            }
        } else {
            let ty = self.map_ty(rty);
            match int_scalar_bits(&ty) {
                Some((b, _)) => (ty, b),
                None => return None,
            }
        };
        // Trust: rust 1.99 — `ty::AliasConst` replaces the removed `ty::UnevaluatedConst`
        // (see `lower_named_const` above; identical adaptation).
        let uv = ty::AliasConst::new(
            self.tcx,
            ty::AliasConstKind::new_from_def_id(self.tcx, def_id),
            args,
        );
        let uv = self.tcx.erase_and_anonymize_regions(uv);
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let valtree = match self.tcx.const_eval_resolve_for_typeck(typing_env, uv, span) {
            Ok(Ok(v)) => v,
            _ => return None,
        };
        let value = ty::Value { ty: rty, valtree };
        if is_bool {
            return value.try_to_bool().map(|b| (Ty::Bool, Constant::Bool(b)));
        }
        let raw = value.try_to_bits(self.tcx, typing_env)?;
        if is_float {
            // Same faithfulness guard as `lower_named_const`: the f64 carrier must round-trip the
            // source IEEE bits EXACTLY (a signaling/non-canonical f32 NaN the `f32 as f64`
            // widening quiets is declined — never promote a value whose bits differ from the
            // const's true value).
            let v: f64 = match bits {
                32 => {
                    let carrier = f64::from(f32::from_bits(raw as u32));
                    if (carrier as f32).to_bits() != raw as u32 {
                        return None;
                    }
                    carrier
                }
                64 => {
                    let carrier = f64::from_bits(raw as u64);
                    if carrier.to_bits() != raw as u64 {
                        return None;
                    }
                    carrier
                }
                _ => return None,
            };
            return Some((ty, Constant::Float(v)));
        }
        Some((ty, integer_constant_from_bits(raw, signed, bits)))
    }

    /// Trust (wave-AR): COMPACT lowering for a LARGE constant array-repeat `[c; N]`
    /// (`N >= REPEAT_COMPACT_MIN`) — ONE `Inst::Const { ty: Ty::Array(TyId, N), value:
    /// Constant::Array([c; N]) }` instead of the legacy `Ty::Tuple([T; N])` seed + N
    /// `InsertField`s. The legacy expansion is O(N^2) MEMORY (N+1 instructions, each carrying an
    /// O(N) `Ty::Tuple` that `Function::clone` at `crate_module::record` re-clones): measured
    /// 1.4GB peak RSS at N=4096 and 5.3GB at 8192, so the real aterm-grid `[0; PAGE_SIZE]`
    /// (`Page::new`, PAGE_SIZE = 64*1024) needs ~100GB per body and wedges the whole-crate dump.
    /// The compact form is O(N) in ONE instruction (the replicated constant element) and O(1) in
    /// the TYPE — `Ty::Array(pend_ty(elem), N)`, the ZERO-LENGTH arm's exact spelling and the
    /// MIR-side oracle's convention (`map_type_ctx`) for ALL N — so cloning the function is
    /// O(instructions), never O(N^2).
    ///
    /// SEMANTICS preserved: the element is lowered ONCE (rustc evaluates the repeat operand even
    /// when its value is then encoded into a constant, so any trap it carries stays on the
    /// path — the zero-length arm's exact discipline), with the same borrow-ptr escape guard as
    /// the legacy path; the emitted constant replicates its value into exactly the N slots the
    /// legacy `InsertField` chain would have written. The pinned interpreter materializes
    /// `(Ty::Array, Constant::Array)` with an exact length check (interpret.rs `constant_to_value`,
    /// the zero-length arm's precedent), and the splice already remaps `Ty::Array(TyId, N)` for
    /// ANY N (`ty_spliceable` / `remap_ty` / `type_entry_ok` — in place since the wave-17 bytes
    /// global). The pended element type is a bare scalar, so the types-table entry is table-free
    /// (`type_entry_ok`) and trivially fn-ptr-free (the zero-length arm's `ty_contains_func`
    /// wall, vacuous for scalars).
    ///
    /// THRESHOLD (`REPEAT_COMPACT_MIN`): the compact spelling changes the emitted IR SHAPE, and
    /// every existing supported repeat in the probe/acceptance corpus is small — gating on N
    /// keeps every existing dump byte-identical (one-level targets, the PAGE_SIZE=256 real-grid
    /// fallback copy) while the pathological sizes take the O(N) form. Coverage semantics above
    /// the threshold are unchanged for the supported fragment (a scalar CONSTANT element); the
    /// one deliberate narrowing is a large repeat of a NON-CONSTANT element, which the legacy
    /// path "supported" only in principle (the O(N^2) wedge means the compile never finished, so
    /// no dump ever carried one) and which now fails closed with a precise reason instead.
    ///
    /// FAIL-CLOSED: a non-`ty::Array` expr type; an element type that does not map cleanly or is
    /// not a seedable scalar (int/bool/float — `seed_constant`'s exact set); an unsupported /
    /// borrow-ptr element value; and an element value that is not a block-local scalar
    /// `Inst::Const` of exactly the element type — notably the deferred-local-const
    /// `Constant::PhantomData` sentinel, whose value is unknown here and is patched exactly ONCE
    /// at finalize (`crate_module::patch_placeholder`), so replicating it N times would dump N
    /// forever-wrong values.
    fn lower_repeat_compact(
        &mut self,
        span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        value: ExprId,
        n: u64,
    ) -> Option<ValueId> {
        // Map ONLY the element type — never N copies of it (the whole point).
        let ty::Array(elem_rty, _) = expr_ty.kind() else {
            self.unsupported.push((format!("{span:?}"), "Repeat(compact non-array ty)"));
            return None;
        };
        let Some(elem_ty) = self.map_ty_checked(*elem_rty) else {
            // `map_ty` recorded its own precise `Ty(...)` reason; add the arm marker so the
            // coverage row names the construct.
            self.unsupported.push((format!("{span:?}"), "Repeat(compact element ty)"));
            return None;
        };
        if seed_constant(&elem_ty).is_none() {
            self.unsupported.push((format!("{span:?}"), "Repeat(compact non-scalar element)"));
            return None;
        }
        // Lower the element ONCE (trap preservation), same escape guards as the legacy path.
        let elem = match self.lower_expr(value) {
            Some(v) => {
                if self.is_borrow_ptr(v) {
                    self.unsupported.push((format!("{span:?}"), "Repeat(borrow ptr element)"));
                    return None;
                }
                v
            }
            None => {
                self.unsupported.push((format!("{span:?}"), "Repeat(unsupported element)"));
                return None;
            }
        };
        // The element VALUE must resolve to a scalar constant defined in the OPEN block (a
        // literal / eagerly-evaluated named const). Anything else — a runtime value, a merge
        // block-param, an earlier-block def, the PhantomData deferral sentinel — fails closed:
        // the compact form ENCODES the value N times, so only a right-here-known constant of
        // exactly the element type is faithful.
        let elem_const = self.cur.iter().rev().find_map(|node| {
            if node.results.first() != Some(&elem) {
                return None;
            }
            match &node.inst {
                Inst::Const {
                    ty,
                    value: c @ (Constant::Int(_) | Constant::Bool(_) | Constant::Float(_)),
                } if *ty == elem_ty => Some(c.clone()),
                _ => None,
            }
        });
        let Some(c) = elem_const else {
            self.unsupported.push((format!("{span:?}"), "Repeat(compact non-const element)"));
            return None;
        };
        let res = self.fresh();
        let elem_tid = self.pend_ty(elem_ty);
        self.push_node(InstrNode::new(Inst::Const {
                ty: Ty::Array(elem_tid, n),
                value: Constant::Array(vec![c; n as usize]),
            })
            .with_result(res),
        );
        Some(res)
    }

    /// Trust: build a runtime array aggregate from already-lowered element values, sharing the exact
    /// tuple/struct machinery. The array `[T; N]` is a `Ty::Tuple([T; N])`; we seed a typed
    /// `Const`-aggregate (interpretable scalar placeholders — NEVER `Inst::Undef`, which the reference
    /// interpreter executes as eager UB) and `InsertField` each element value over it in index order.
    /// FAIL-CLOSED if any element type is non-seedable (`seed_constant_ty` declines): no partial
    /// aggregate. Trust (wave-13): the seed recurses over nested `Ty::Struct`/`Ty::Tuple` element
    /// types (was scalar-only), so an array of structs/tuples seeds a well-typed nested aggregate;
    /// a non-seedable leaf still declines the whole array. Each seed lane is overwritten below.
    fn build_array_aggregate(
        &mut self,
        span: rustc_span::Span,
        array_ty: &Ty,
        elem_tys: &[Ty],
        elem_vals: &[ValueId],
    ) -> Option<ValueId> {
        debug_assert_eq!(elem_tys.len(), elem_vals.len());
        let seed_consts: Vec<Constant> = match elem_tys
            .iter()
            .map(|e| self.seed_constant_ty(e, 0))
            .collect::<Option<Vec<_>>>()
        {
            Some(c) => c,
            None => {
                self.unsupported.push((format!("{span:?}"), "Array(non-scalar element seed)"));
                return None;
            }
        };
        let mut agg = self.fresh();
        self.push_node(InstrNode::new(Inst::Const {
                ty: array_ty.clone(),
                value: Constant::Aggregate(seed_consts),
            })
            .with_result(agg),
        );
        for (i, val) in elem_vals.iter().enumerate() {
            let next = self.fresh();
            self.push_node(InstrNode::new(Inst::InsertField {
                    ty: array_ty.clone(),
                    aggregate: agg,
                    field: i as u32,
                    value: *val,
                })
                .with_result(next),
            );
            agg = next;
        }
        Some(agg)
    }

    /// Trust: materialize a FAITHFUL slice fat pointer `(data_ptr, len)` from an array-to-slice
    /// `PointerCoercion{Unsize}`. `source` is the coercion operand — a `&[T; N]` reference (a
    /// `Borrow{Shared}` of a fixed-size array local). We:
    ///   1. peel the source's `Borrow` to find the array place (a bare local) and its `ty::Array` type;
    ///   2. lower the array VALUE (the `Ty::Tuple([T; N])` aggregate) — this is the exact aggregate the
    ///      construction/index arms build;
    ///   3. `Alloca` a slot of the array tuple type and `Store` the aggregate into it — the slot pointer
    ///      is the REAL in-memory address of the array (the data pointer), NOT a placeholder;
    ///   4. assemble `Ty::Tuple([Ty::Ptr, Ty::I64])` = `(data_ptr, len=N)` via two `InsertField`s over a
    ///      `Const`-seeded `(NullPtr-seed, 0)` aggregate.
    /// The resulting tuple is a plain interpretable aggregate; field 0 (the data ptr) feeds `GEP`+`Load`
    /// on a later `s[i]`, field 1 (the len) feeds `ExtractField` on `s.len()`.
    ///
    /// FAIL-CLOSED: a source that is not a `Borrow{Shared}` of an array LOCAL, a non-`ty::Array` operand
    /// (slice-of-slice / `Vec` / dyn unsizing — those are not the array-to-slice coercion we model), a
    /// non-const array length, a non-scalar element, or an array value that does not lower.
    fn lower_array_to_slice(&mut self, span: rustc_span::Span, source: ExprId) -> Option<ValueId> {
        // Trust (wave-21): a byte-string literal `b"abc"` coerced to a fat `&[u8]` — e.g.
        // `const BAR: &[u8] = b"a\xF0\t"`. The coercion arm has already confirmed this expr's
        // TARGET is a fat `&[T]` slice (`is_slice_ref`); the coercion SOURCE here is the
        // byte-string literal itself, whose own type is the THIN `&'static [u8; N]`
        // (reference-to-sized-array). `array_place_expr` cannot peel that to a local — it bottoms
        // out at `Literal`, not `VarRef` — which is exactly why `b".."` slices used to fail closed
        // as `Unsize(non-array-local source)`. Materialize the `[u8; N]` bytes as a module GLOBAL
        // (`emit_bytes_global`) and assemble the FAT pointer `(data_ptr, len = N)` DIRECTLY: this is
        // the array-to-slice twin of the `&str` string-literal arm (same global, same
        // `build_fat_ptr_from_parts`, same wave-17 faithfulness argument; the length is the byte
        // count). Peel only `Scope`/`Use`: a byte-string literal is ALREADY a reference (no `Borrow`
        // layer), whereas an inline `&[1, 2, 3]` array literal carries a `Borrow{Array}` and is NOT
        // matched here — it bottoms out at a `VarRef`/`Array`, not a `Literal`, so it falls through
        // to the array-place path below unchanged. FAIL-CLOSED on the empty byte string
        // (`emit_bytes_global` rejects `N == 0`), consistent with wave-17.
        //
        // Peel the SAME chain `array_place_expr` peels (`Scope`/`Use`/`Borrow{Shared|Fake}`/`Deref`):
        // rustc forms the `&[u8; N]` coercion operand as `&*b".."` — the THIR is
        // `Borrow{Shared, Deref{Literal{ByteStr}}}`, so the byte-string literal is NOT the bare
        // source but sits under a shared-borrow-of-deref reborrow. A byte-string literal at the
        // BOTTOM (vs a `VarRef` local, which `array_place_expr` handles) is the A1 case.
        {
            let mut lit_src = source;
            loop {
                match &self.thir.exprs[lit_src].kind {
                    ExprKind::Scope { value, .. } => lit_src = *value,
                    ExprKind::Use { source } => lit_src = *source,
                    ExprKind::Borrow {
                        borrow_kind:
                            rustc_middle::mir::BorrowKind::Shared
                            | rustc_middle::mir::BorrowKind::Fake(_),
                        arg,
                    } => lit_src = *arg,
                    ExprKind::Deref { arg } => lit_src = *arg,
                    _ => break,
                }
            }
            if let ExprKind::Literal { lit, .. } = &self.thir.exprs[lit_src].kind {
                if let LitKind::ByteStr(bytes_sym, _) = lit.node {
                    let bytes: Vec<u8> = bytes_sym.as_byte_str().to_vec();
                    return match self.emit_bytes_global(&bytes) {
                        Some(data_ptr) => {
                            // Trust (B2-1): the coerced `&[u8]` is first-class
                            // `Ty::FatPtr(Slice(U8))` — canonical U64 length +
                            // `PtrFromParts` (the tuple chain retires for this lane).
                            let len_val = self.fresh();
                            self.push_node(InstrNode::new(Inst::Const {
                                    ty: Ty::U64,
                                    value: Constant::Int(bytes.len() as i128),
                                })
                                .with_result(len_val),
                            );
                            self.build_slice_fat_value(Ty::U8, data_ptr, len_val)
                        }
                        None => {
                            self.unsupported
                                .push((format!("{span:?}"), "Unsize(empty byte-string)"));
                            None
                        }
                    };
                }
            }
        }
        // The coercion source is a `&[T; N]` reference to an array PLACE. rustc wraps the array
        // place in an autoref/autoderef chain — `Borrow{Shared, Deref{Borrow{Shared, VarRef(a)}}}` —
        // so we peel `Borrow`/`Deref`/`Scope`/`Use` down to the underlying array local `VarRef(a)`
        // (the scalar `Borrow`/`Deref` arms would reject a non-scalar array pointee, so we must not
        // route the chain through them). FAIL-CLOSED if the chain does not bottom out at a local.
        let arr_place = match self.array_place_expr(source) {
            Some(v) => v,
            None => {
                // Trust (totality): before failing closed, try the INLINE ARRAY
                // LITERAL shape — `&[a, b, c]` coerced to `&[T]`. This is the
                // single largest producer wall on real code (461 of
                // regex-syntax's const-init bodies fail here and on nothing
                // else: every `pub const V: &'static [T] = &[..]` unicode
                // table). It has no array LOCAL, so `array_place_expr` /
                // `build_slice_fat_ptr` — which read a bound local's current
                // value — cannot serve it.
                //
                // FAITHFUL, and by the same construction the local path uses:
                // lower the literal to the `Ty::Tuple([T; N])` aggregate the
                // `ExprKind::Array` arm already builds, `Alloca` a slot of that
                // type, `Store` the aggregate, and take the slot pointer as the
                // REAL data address. rustc materializes exactly this (an
                // in-memory temporary holding the array, borrowed as the slice
                // data pointer); the only difference from the local path is
                // where the aggregate came from, and both are the same lowered
                // value. Every downstream gate is preserved: a non-`ty::Array`
                // operand, a non-const length, a non-scalar element, or an
                // array value that does not lower each keep their own precise
                // fail-closed tag.
                return self.lower_inline_array_to_slice(span, source);
            }
        };
        self.build_slice_fat_ptr(span, arr_place)
    }

    /// Trust (totality): the inline-array-literal twin of [`Self::build_slice_fat_ptr`] —
    /// `&[a, b, c]` coerced to `&[T]`, where there is no array local to read.
    /// Peels `Scope`/`Use`/`Borrow` to an `ExprKind::Array`/`Repeat`, lowers it as a
    /// VALUE (the same aggregate the construction arm builds), then Alloca+Store+
    /// fat-pointer exactly as the local path does. `None` (with a precise tag) for
    /// anything else.
    fn lower_inline_array_to_slice(
        &mut self,
        span: rustc_span::Span,
        source: ExprId,
    ) -> Option<ValueId> {
        // Peel to the array-literal expression.
        let mut e = source;
        let arr_expr = loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::Use { source } => e = *source,
                ExprKind::Borrow { arg, .. } => e = *arg,
                // MEASURED (not assumed): rustc's array-to-slice coercion wraps the
                // literal as `Deref{ Borrow{ Array } }` — a temporary diagnostic
                // printing the real `ExprKind` at this fallthrough reported
                // `kind=Deref`, after two wrong hypotheses about this shape.
                ExprKind::Deref { arg } => e = *arg,
                ExprKind::Array { .. } | ExprKind::Repeat { .. } => break e,
                _ => {
                    self.unsupported.push((format!("{span:?}"), "Unsize(non-array-local source)"));
                    return None;
                }
            }
        };
        // The literal's own type must be a concrete `[T; N]` with a scalar element —
        // the same three gates `build_slice_fat_ptr` applies, kept verbatim so the
        // two paths accept exactly the same shapes.
        let arr_rty = self.thir.exprs[arr_expr].ty;
        let (elem_rty, len) = match arr_rty.kind() {
            ty::Array(elem, len) => match len.try_to_target_usize(self.tcx) {
                Some(n) => (*elem, n),
                None => {
                    self.unsupported.push((format!("{span:?}"), "Slice(array non-const len)"));
                    return None;
                }
            },
            _ => {
                self.unsupported.push((format!("{span:?}"), "Slice(non-array operand)"));
                return None;
            }
        };
        let elem_ty = self.map_ty(elem_rty);
        if !is_scalar_ty(&elem_ty) {
            self.unsupported.push((format!("{span:?}"), "Slice(non-scalar element)"));
            return None;
        }
        let array_ty = Ty::Tuple(vec![elem_ty.clone(); len as usize]);
        // Lower the literal as a value (the `ExprKind::Array`/`Repeat` arm).
        let arr_val = self.lower_expr(arr_expr)?;
        let data_ptr = self.fresh();
        self.push_node(InstrNode::new(Inst::Alloca { ty: array_ty.clone(), count: None, align: None })
                .with_result(data_ptr),
        );
        self.push_node(InstrNode::new(Inst::Store {
            ty: array_ty,
            ptr: data_ptr,
            value: arr_val,
            volatile: false,
            align: None,
        }));
        let len_val = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(len as i128) })
                .with_result(len_val),
        );
        self.build_slice_fat_value(elem_ty, data_ptr, len_val)
    }

    /// Trust: build the FAITHFUL slice fat pointer `Ty::Tuple([Ty::Ptr, Ty::I64]) = (data_ptr, len)`
    /// for the array PLACE `arr_place` (a bare `VarRef` local of type `[T; N]`). Shared by the unsize
    /// coercion (`let s: &[T] = &a`) and the full-range-index slice (`&a[..]`). We:
    ///   1. read the array local's CURRENT `Ty::Tuple([T; N])` aggregate value;
    ///   2. `Alloca` a slot of the array tuple type and `Store` the aggregate — the slot pointer is the
    ///      REAL in-memory address of the array (the data pointer), NOT a placeholder;
    ///   3. assemble `(data_ptr, len=N)` via two `InsertField`s over a `(PhantomData-seed, 0)` aggregate
    ///      (the seed lanes are immediately overwritten by the real data ptr / len).
    /// Field 0 (the data ptr) later feeds `GEP`+`Load` on `s[i]`; field 1 (the len) feeds
    /// `ExtractField` on `s.len()`.
    ///
    /// FAIL-CLOSED: a non-local array place, a non-`ty::Array` operand (slice-of-slice / `Vec` / dyn —
    /// not the array-to-slice coercion we model), a non-const length, a non-scalar element, or an
    /// unbound / borrow-ptr array value.
    fn build_slice_fat_ptr(
        &mut self,
        span: rustc_span::Span,
        arr_place: ExprId,
    ) -> Option<ValueId> {
        let arr_local = match self.place_local(arr_place) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Slice(array place not a local)"));
                return None;
            }
        };
        // The operand must be a fixed-size array (`[T; N]`); slices / Vec / dyn fail closed.
        let arr_rty = self.thir.exprs[arr_place].ty;
        let (elem_rty, len) = match arr_rty.kind() {
            ty::Array(elem, len) => match len.try_to_target_usize(self.tcx) {
                Some(n) => (*elem, n),
                None => {
                    self.unsupported.push((format!("{span:?}"), "Slice(array non-const len)"));
                    return None;
                }
            },
            _ => {
                self.unsupported.push((format!("{span:?}"), "Slice(non-array operand)"));
                return None;
            }
        };
        // Only scalar-element arrays round-trip through memory in this slice.
        let elem_ty = self.map_ty(elem_rty);
        if !is_scalar_ty(&elem_ty) {
            self.unsupported.push((format!("{span:?}"), "Slice(non-scalar element)"));
            return None;
        }
        let array_ty = Ty::Tuple(vec![elem_ty.clone(); len as usize]);
        // Read the array local's CURRENT aggregate value directly (the `Ty::Tuple([T; N])` the
        // construction arms built and bound). We read the local rather than re-lowering the place
        // expression so the non-scalar `Borrow`/`Deref` chain is never traversed.
        let arr_val = match self.local_value(arr_local) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Slice(array local unbound)"));
                return None;
            }
        };
        if self.is_borrow_ptr(arr_val) {
            self.unsupported.push((format!("{span:?}"), "Slice(array is borrow ptr)"));
            return None;
        }
        // Alloca + Store the array aggregate; the slot pointer is the REAL data address.
        let data_ptr = self.fresh();
        self.push_node(InstrNode::new(Inst::Alloca { ty: array_ty.clone(), count: None, align: None })
                .with_result(data_ptr),
        );
        self.push_node(InstrNode::new(Inst::Store {
            ty: array_ty,
            ptr: data_ptr,
            value: arr_val,
            volatile: false,
            align: None,
        }));
        // Trust (B2-1): len as the canonical U64 metadata constant, and the fat value
        // assembled via the FORMAT's own constructor (`PtrFromParts`) at the first-class
        // `Ty::FatPtr(Slice)` type — retiring the tuple seed + InsertField chain here.
        let len_val = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(len as i128) })
                .with_result(len_val),
        );
        self.build_slice_fat_value(elem_ty, data_ptr, len_val)
    }

    /// Trust (B2-1): assemble a first-class slice fat pointer
    /// `Ty::FatPtr(FatPtrKind::Slice(elem))` from an ALREADY-computed data pointer
    /// (`Ty::Ptr`) and a U64 length, via the FORMAT's own `Inst::PtrFromParts`. The
    /// interpreter executes it as the two-lane fat value (data lane feeds `PtrData` +
    /// `GEP`/`Load` on `s[i]`, metadata lane feeds `PtrMetadata` on `s.len()`).
    fn build_slice_fat_value(
        &mut self,
        elem_ty: Ty,
        data_ptr: ValueId,
        len_val: ValueId,
    ) -> Option<ValueId> {
        let tid = self.pend_ty(elem_ty);
        let fat_ty = Ty::FatPtr(trust_ir::FatPtrKind::Slice(tid));
        let fat = self.fresh();
        self.push_node(InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat_ty,
                metadata_ty: Ty::U64,
                data: data_ptr,
                metadata: len_val,
            })
            .with_result(fat),
        );
        Some(fat)
    }

    /// Trust (wave-17): materialize a `[u8; N]` bytes module GLOBAL holding `bytes` and emit an
    /// `Inst::GlobalAddr` yielding its `'static` data pointer (a `Ty::Ptr`). Reuses the wave-16
    /// pending-globals machinery: the `Global` is pushed onto `self.pending_globals` (flushed into
    /// the single-function module in body order at `finish_body`, so its `GlobalId` is its pend
    /// index) and its element type `Ty::U8` is interned into the per-body `types` table via
    /// `pend_ty` (the `Ty::Array(TyId, N)` element is table-indexed). Name is index-based (byte
    /// deterministic — no timestamp/random); `crate_module` renames it crate-uniquely on splice.
    ///
    /// FAIL-CLOSED (`None`, caller keeps the `Literal(non-int/bool)` tag): an EMPTY byte sequence
    /// (`N == 0`) — a zero-length array global is not proven faithful end-to-end, so `""` / `b""`
    /// stay a missed clean-rate opportunity rather than a guessed lowering.
    fn emit_bytes_global(&mut self, bytes: &[u8]) -> Option<ValueId> {
        if bytes.is_empty() {
            return None;
        }
        let elem_tid = self.pend_ty(Ty::U8);
        let array_ty = Ty::Array(elem_tid, bytes.len() as u64);
        let init = Constant::Array(bytes.iter().map(|b| Constant::Int(*b as i128)).collect());
        let idx = self.pending_globals.len();
        self.pending_globals.push(Global {
            name: format!("__trust_bytes_{idx}"),
            ty: array_ty,
            mutable: false,
            initializer: Some(init),
            linkage: Linkage::Internal,
            tls: None,
            // No explicit over-alignment: a byte array is 1-aligned by type.
            align: None,
        });
        let global = GlobalId::new(idx as u32);
        let data_ptr = self.fresh();
        self.push_node(InstrNode::new(Inst::GlobalAddr { global }).with_result(data_ptr));
        Some(data_ptr)
    }

    /// Trust: recognize and lower a SLICE `s.len()` call. Returns `Some(len_value)` iff `fun` resolves
    /// to the `slice_len_fn` lang item (the `<[T]>::len` method) with exactly one receiver argument that
    /// lowers to the slice fat pointer. The length is `ExtractField(slice, 1)` (the `I64` len lane),
    /// reinterpreted to the `usize`-mapped result type (both 64-bit on a 64-bit target — a same-width
    /// `Cast` identity). Returns `None` (NOT an `unsupported` push) for any non-`len` call, so the
    /// caller falls through to the normal direct-call path unchanged.
    ///
    /// FAIL-CLOSED (records `unsupported`, returns `None`'s sentinel as a real gap) only once we have
    /// COMMITTED to the `len` shape but cannot complete it: a non-1-arg signature, a receiver that does
    /// not lower, or a non-integer result type.
    fn try_lower_slice_len(
        &mut self,
        span: rustc_span::Span,
        result_rty: RustcTy<'tcx>,
        fun: ExprId,
        args: &[ExprId],
        from_hir_call: bool,
    ) -> Option<ValueId> {
        if !from_hir_call {
            return None;
        }
        // Peel Scope/Use to the callee operand and resolve its `ty::FnDef` def_id.
        let mut f = fun;
        loop {
            match &self.thir.exprs[f].kind {
                ExprKind::Scope { value, .. } => f = *value,
                ExprKind::Use { source } => f = *source,
                _ => break,
            }
        }
        let def_id = match self.thir.exprs[f].ty.kind() {
            ty::FnDef(def_id, _) => *def_id,
            _ => return None,
        };
        // Must be the `<[T]>::len` lang item — not any other method.
        if self.tcx.lang_items().slice_len_fn() != Some(def_id) {
            return None;
        }
        // Committed to the `len` shape: it takes exactly the slice receiver.
        if args.len() != 1 {
            self.unsupported.push((format!("{span:?}"), "SliceLen(unexpected arity)"));
            return None;
        }
        let result_ty = self.map_ty(result_rty);
        if int_scalar_bits(&result_ty).is_none() {
            self.unsupported.push((format!("{span:?}"), "SliceLen(non-int result ty)"));
            return None;
        }
        // The `len` receiver is `&self` where `Self = [T]` — rustc forms it as a reborrow of the slice
        // local, `Borrow{Shared, Deref{VarRef(s)}}` (type `&[T]`). Peel the reborrow to the slice VALUE
        // expr so we lower the fat-pointer tuple directly (not the scalar `Borrow{non-local}` path).
        let recv = self.slice_value_expr(args[0]);
        let slice_val = match self.lower_expr(recv) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "SliceLen(unsupported receiver)"));
                return None;
            }
        };
        // Trust (B2-1): the receiver is now first-class `Ty::FatPtr(Slice)` — the len
        // is the metadata lane, read via the FORMAT's own projection (`PtrMetadata`,
        // canonical metadata type = the pointer-sized unsigned U64). A receiver whose
        // mapped type is NOT the fat spelling (e.g. its element failed to map) keeps
        // the fail-closed receiver tag.
        let fat_ty = self.map_ty(self.thir.exprs[recv].ty);
        if !matches!(fat_ty, Ty::FatPtr(_)) {
            self.unsupported.push((format!("{span:?}"), "SliceLen(unsupported receiver)"));
            return None;
        }
        let len_u64 = self.fresh();
        self.push_node(InstrNode::new(Inst::PtrMetadata {
                ptr_ty: fat_ty,
                metadata_ty: Ty::U64,
                ptr: slice_val,
            })
            .with_result(len_u64),
        );
        // Reinterpret the U64 len to the `usize`-mapped result type — a same-width
        // reinterpret (`CastOp::Trunc` is the equal-width identity in the interpreter,
        // matching the numeric-`Cast` arm).
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U64,
                dst_ty: result_ty,
                operand: len_u64,
            })
            .with_result(res),
        );
        Some(res)
    }

    /// Trust (wave-N): fold ONE `offset_of!` field level to a compile-time `usize` `Inst::Const`.
    /// rustc's THIR builder (`thir/cx/expr.rs`, `hir::ExprKind::OffsetOf`) lowers each level of a
    /// field path to a synthetic `Call` to the `OffsetOf` lang-item intrinsic —
    /// `FnDef(offset_of, [Container])` with two `u32` `NonHirLiteral` args `[variant, field]`,
    /// `from_hir_call = false` — and chains nested levels with `Add`, so the normal `Add` lowering
    /// sums the levels and this recognizer handles exactly one call. The offset is READ from rustc's
    /// AUTHORITATIVE layout, MIRRORING the offset_of intrinsic const-eval
    /// (`rustc_const_eval interpret/intrinsics.rs`, `sym::offset_of`):
    /// `layout_of(C).for_variant(variant).fields.offset(field).bytes()` — never hand-computed, so the
    /// const is byte-identical to what built MIR evaluates for the same intrinsic (→ flippable, no
    /// `Inst::Call`, body stays interpretable). Callers gate on the callee being the offset_of lang
    /// item, so reaching here means it IS offset_of: FAIL-CLOSED with a precise tag (returns `None`)
    /// on a param-bearing/opaque container or a `layout_of` error (offset not layout-stable), never
    /// a silent guess.
    fn lower_offset_of(
        &mut self,
        span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        fun: ExprId,
        args: &[ExprId],
    ) -> Option<ValueId> {
        let ty::FnDef(_, gen_args) = self.thir.exprs[fun].ty.kind() else {
            return None;
        };
        if args.len() != 2 {
            // The synthetic offset_of call is always `(variant: u32, field: u32)`.
            self.unsupported.push((format!("{span:?}"), "OffsetOf(unexpected arity)"));
            return None;
        }
        let container = gen_args.type_at(0);
        // `layout_of` needs a concrete container and can query-cycle from inside `mir_built` while
        // resolving an opaque/generic input. Fail closed before touching the query.
        if !layout_query_is_reentrant_safe(container) {
            self.unsupported.push((format!("{span:?}"), "OffsetOf(non-concrete container)"));
            return None;
        }
        // The two synthetic args are 32-bit `NonHirLiteral` int consts.
        let (Some(variant), Some(field)) =
            (self.read_u32_literal(args[0]), self.read_u32_literal(args[1]))
        else {
            self.unsupported.push((format!("{span:?}"), "OffsetOf(non-literal index)"));
            return None;
        };
        // MIRROR rustc's offset_of const-eval exactly (authoritative — never re-derived).
        let te = ty::TypingEnv::fully_monomorphized();
        let layout = match cycle_safe_layout_of(self.tcx, te, container) {
            Some(l) => l,
            None => {
                self.unsupported.push((format!("{span:?}"), "OffsetOf(layout error)"));
                return None;
            }
        };
        let cx = ty::layout::LayoutCx::new(self.tcx, te);
        let variant_layout = layout.for_variant(&cx, rustc_abi::VariantIdx::from_u32(variant));
        // `FieldsShape::offset` panics out of range — tag the body unsupported
        // instead of aborting the compile (producer totality).
        if field as usize >= variant_layout.fields.count() {
            self.unsupported.push((format!("{span:?}"), "OffsetOf(field outside layout shape)"));
            return None;
        }
        let offset = variant_layout.fields.offset(field as usize).bytes();
        // Emit as the call's result type (`usize` → `map_ty` → U64). No `Inst::Call`.
        let ty = self.map_ty(expr_ty);
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty, value: Constant::Int(offset as i128) })
                .with_result(res),
        );
        Some(res)
    }

    /// Trust (wave-N): read a `u32` from a THIR `NonHirLiteral` int expr (peeling `Scope`), or `None`
    /// if it is not a plain 32-bit int literal. Used only by `lower_offset_of` for the synthetic
    /// `(variant, field)` args rustc emits as 32-bit `ScalarInt` `NonHirLiteral`s.
    fn read_u32_literal(&self, e: ExprId) -> Option<u32> {
        let mut e = e;
        loop {
            match &self.thir.exprs[e].kind {
                ExprKind::Scope { value, .. } => e = *value,
                ExprKind::NonHirLiteral { lit, .. } => {
                    return lit.try_to_bits(rustc_abi::Size::from_bits(32)).ok().map(|b| b as u32);
                }
                _ => return None,
            }
        }
    }

    /// Trust: lower a SLICE index `s[i]` (FAITHFUL fat-pointer read). `place` is the `[T]` slice place
    /// (a `Deref` of the `&[T]` fat-pointer value); `index` is the element index; `elem_rty` is the
    /// result (element) type. We:
    ///   1. peel `place`'s `Deref` to the slice VALUE expr and lower it to the `Tuple([Ptr, I64])`;
    ///   2. `ExtractField 0` → the data pointer (`Ty::Ptr`, a real in-memory array address);
    ///   3. lower `index` to an `I64`-domain `ValueId` (the static `GEP` index needs an integer value);
    ///   4. `GEP { pointee_ty: elem_ty, base: data_ptr, indices: [idx] }` → element address;
    ///   5. `Load { ty: elem_ty }` from it. An out-of-bounds index makes the `Load` trap, matching MIR's
    ///      bounds-check panic (the differential treats matching traps as agreement).
    ///
    /// FAIL-CLOSED: a `place` that is not a `Deref` of a slice value, a non-scalar element type, an
    /// unsupported slice/index value, or a borrow-ptr index.
    fn lower_slice_index(
        &mut self,
        span: rustc_span::Span,
        elem_rty: RustcTy<'tcx>,
        place: ExprId,
        index: ExprId,
    ) -> Option<ValueId> {
        let elem_ty = self.map_ty(elem_rty);
        if !is_scalar_ty(&elem_ty) {
            self.unsupported.push((format!("{span:?}"), "SliceIndex(non-scalar element ty)"));
            return None;
        }
        // The slice place is `*slice_value`; peel the `Deref` to the slice VALUE expr.
        let slice_expr = match self.deref_place_arg(place) {
            Some(e) => e,
            None => {
                self.unsupported.push((format!("{span:?}"), "SliceIndex(non-deref slice place)"));
                return None;
            }
        };
        let slice_val = match self.lower_expr(slice_expr) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "SliceIndex(unsupported slice value)"));
                return None;
            }
        };
        // Trust (B2-1): the slice value is first-class `Ty::FatPtr(Slice)` — the data
        // pointer is its data lane, read via the FORMAT's own projection (`PtrData`).
        // Fail closed if the mapped type is not the fat spelling.
        let fat_ty = self.map_ty(self.thir.exprs[slice_expr].ty);
        if !matches!(fat_ty, Ty::FatPtr(_)) {
            self.unsupported.push((format!("{span:?}"), "SliceIndex(unsupported slice value)"));
            return None;
        }
        let data_ptr = self.fresh();
        self.push_node(InstrNode::new(Inst::PtrData { ptr_ty: fat_ty, ptr: slice_val }).with_result(data_ptr),
        );
        // Lower the index. GEP scales each index by `byte_size(elem_ty)`, so the index value must be an
        // integer in the same domain — `usize` maps to a fixed-width int, which is what we want.
        let idx_val = match self.lower_expr(index) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "SliceIndex(unsupported index)"));
                return None;
            }
        };
        if self.is_borrow_ptr(idx_val) {
            self.unsupported.push((format!("{span:?}"), "SliceIndex(borrow ptr index)"));
            return None;
        }
        // GEP to element `index`: base + index * size_of(elem_ty).
        let elem_ptr = self.fresh();
        self.push_node(InstrNode::new(Inst::GEP {
                pointee_ty: elem_ty.clone(),
                base: data_ptr,
                indices: vec![idx_val],
                inbounds: false,
            })
            .with_result(elem_ptr),
        );
        // Load the element (an OOB address traps here — MIR's bounds-check panic equivalent).
        let res = self.fresh();
        self.push_node(InstrNode::new(Inst::Load { ty: elem_ty, ptr: elem_ptr, volatile: false, align: None })
                .with_result(res),
        );
        Some(res)
    }

    /// Trust: if the array-index expression `index` is a CONSTANT non-negative integer literal `K`,
    /// return `K` as a `u32` field offset (for the `ExtractField` constant-index fast-path). Returns
    /// `None` for any runtime/dynamic index (which routes to the `ExtractElement` dynamic path), a
    /// negative literal, or a literal that does not fit a `u32` offset. We peel `Scope`/`Use` wrappers.
    fn const_index_value(&self, mut index: ExprId) -> Option<u32> {
        loop {
            match &self.thir.exprs[index].kind {
                ExprKind::Scope { value, .. } => index = *value,
                ExprKind::Use { source } => index = *source,
                ExprKind::Literal { lit, neg } => {
                    if *neg {
                        return None;
                    }
                    if let LitKind::Int(v, _) = lit.node {
                        return u32::try_from(v.get()).ok();
                    }
                    return None;
                }
                _ => return None,
            }
        }
    }

    /// Trust: lower GENERAL-enum CONSTRUCTION — a variant of an enum the legacy `(tag, payload)`
    /// Trust: lower first-class enum construction into the pinned
    /// interpreter's first-class `Ty::Enum` convention (scratch-verified, cmtest w5_enum (1)/(4)/(5)):
    ///
    /// ```text
    ///   %seed = Const Enum(eid) = Aggregate([Int(<disc of variant>), <per-field scalar seeds>])
    ///   %agg  = InsertField %seed .(1+i) <- <field i value>     (one per payload field)
    /// ```
    ///
    /// The seed's leading `Int` is the DISCRIMINANT VALUE (the interpreter resolves the variant
    /// by value against the `EnumDef`'s effective discriminants and types the tag lane with the
    /// CANONICAL tag repr); the in-register value is `Aggregate([tag, fields...])` shaped by the
    /// SELECTED variant, so payload slots insert/extract positionally at `1 + field_index`.
    /// Every ingredient (field types, discriminant) is read from the REGISTERED `EnumDef` —
    /// single source of truth shared with `lower_enum_match_general`'s `Switch` cases.
    ///
    /// FAIL-CLOSED: an enum `register_enum` declined (the mapped type is not `Ty::Enum`; its own
    /// tag was recorded), an unregistered id (impossible for a fresh `map_ty` result — checked
    /// anyway), a field-count/index mismatch, a non-seedable field seed (defensive — the
    /// registration gate already walls these), or any field value that is unsupported / a borrow
    /// pointer.
    fn lower_enum_construct_general(
        &mut self,
        span: rustc_span::Span,
        expr_ty: RustcTy<'tcx>,
        variant_index: rustc_abi::VariantIdx,
        field_exprs: &[(usize, ExprId)],
    ) -> Option<ValueId> {
        // The mapped type registers (or re-finds) the EnumDef; bail if it degraded.
        let enum_ty = self.map_ty(expr_ty);
        // Trust (wave-SEAM): the OPTION-DISCRIMINANT VALUE-LANE constructor. Under
        // `TRUST_OPTION_FLAG_LANES=1` an opaque-lane `Option` maps `Ty::Bool` (map_ty's enum
        // arm — exactly the field lanes' registration type), and a literal `None`/`Some(..)`
        // in VALUE position lowers as that discriminant constant: `None` → `const bool
        // false`, `Some(..)` → `const bool true`. The `Some` PAYLOAD expression is
        // deliberately NOT lowered — identical to the field WRITE side's ctor-store posture
        // (which drops the whole payload expr; CLEAN-ONLY) — and `contains_call` is FORCED
        // for both variants: the lane is an abstraction, so the body must stay structurally
        // `NotRun` (never interpreted/flipped — the eager-UB/flip-differential guard the
        // read side and the let-test lane already practice). The value joins the
        // `option_lane_values` ledger: it is a PROVEN discriminant, admissible as an
        // `if let Some(..)` value-lane scrutinee. Admission is EXACT: the mapped ty must be
        // the flag's `Ty::Bool` AND the ADT the Option lang item — every other enum whose
        // mapped ty is non-enum keeps the fail-closed decline verbatim (flag off:
        // byte-identical, the mapped ty is `Ty::Unit` there).
        if matches!(enum_ty, Ty::Bool)
            && option_flag_lanes_enabled()
            && matches!(expr_ty.kind(), ty::Adt(a, _)
                if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
        {
            // Option's variant order is fixed by core: None = 0, Some = 1.
            let is_some = variant_index.as_u32() == 1;
            self.contains_call = true;
            let res = self.fresh();
            self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(is_some) })
                    .with_result(res),
            );
            self.option_lane_values.push(res);
            return Some(res);
        }
        let Ty::Enum(eid) = &enum_ty else {
            self.unsupported.push((format!("{span:?}"), "EnumCtor(non-enum mapped ty)"));
            return None;
        };
        // Snapshot the variant's declared field types + this variant's discriminant out of the
        // registered def (clone: the `&mut self` calls below would hold the borrow).
        let (field_tys, disc) = match self.registered_enum(*eid) {
            Some(ed) => {
                let Some(variant) = ed.variants.get(variant_index.as_usize()) else {
                    self.unsupported.push((format!("{span:?}"), "EnumCtor(variant index OOB)"));
                    return None;
                };
                let Some(disc) = ed.discriminants.get(variant_index.as_usize()).copied().flatten()
                else {
                    // register_enum stores every discriminant explicitly; missing = desync.
                    self.unsupported.push((format!("{span:?}"), "EnumCtor(missing discriminant)"));
                    return None;
                };
                (variant.fields.clone(), disc)
            }
            None => {
                self.unsupported.push((format!("{span:?}"), "EnumCtor(unregistered enum id)"));
                return None;
            }
        };
        if field_exprs.len() != field_tys.len() {
            self.unsupported.push((format!("{span:?}"), "EnumCtor(field-count mismatch)"));
            return None;
        }
        // Lower each field value FIRST (source order — `field_exprs` carries THIR's evaluation
        // order), recording it against its destination payload index; fail-closed on any
        // unsupported/borrow-ptr value or index anomaly — never a partial aggregate.
        let mut field_vals: Vec<Option<ValueId>> = vec![None; field_tys.len()];
        let mut unit_slot_filled: Vec<bool> = vec![false; field_tys.len()];
        for &(idx, fexpr) in field_exprs {
            if idx >= field_tys.len() || field_vals[idx].is_some() || unit_slot_filled[idx] {
                self.unsupported.push((format!("{span:?}"), "EnumCtor(field index anomaly)"));
                return None;
            }
            // Trust (B3-2c E3): a UNIT slot (the DEF field ty — the admission
            // invariant guarantees it means a drop-free ZST) takes the wave-UF
            // triple: lower the expr FOR EFFECTS; a value-less `()` is accepted
            // iff nothing tagged AND the block did not seal (`Some(return 7)`
            // stays fail-closed); a MATERIALIZED non-`()` ZST value (a fmt::Error
            // literal) is lowered then DISCARDED — never inserted into a Unit
            // slot (interpreter TypeError). The PhantomData seed IS the value.
            if matches!(field_tys[idx], Ty::Unit) {
                let mark = self.unsupported.len();
                match self.lower_expr(fexpr) {
                    Some(_zst) => {}
                    None => {
                        if self.unsupported.len() != mark || self.sealed {
                            self.unsupported
                                .push((format!("{span:?}"), "EnumCtor(unit payload unsupported)"));
                            return None;
                        }
                    }
                }
                unit_slot_filled[idx] = true;
                continue;
            }
            match self.lower_expr(fexpr) {
                Some(v) => {
                    if self.is_borrow_ptr(v) {
                        self.unsupported
                            .push((format!("{span:?}"), "EnumCtor(borrow ptr payload)"));
                        return None;
                    }
                    field_vals[idx] = Some(v);
                }
                None => {
                    self.unsupported.push((format!("{span:?}"), "EnumCtor(unsupported payload)"));
                    return None;
                }
            }
        }
        // Every non-unit slot must be filled; unit slots stay value-less (their
        // PhantomData seed is final).
        for (i, fty) in field_tys.iter().enumerate() {
            if !matches!(fty, Ty::Unit) && field_vals[i].is_none() {
                self.unsupported.push((format!("{span:?}"), "EnumCtor(missing field)"));
                return None;
            }
        }
        // Typed `Const` enum seed: [disc, per-field placeholders] (registration walls
        // the fields to seedable scalars OR canonical Unit; the recursive
        // seed_constant_ty supplies PhantomData for Unit — the wave-UF seed. The
        // interpreter's arity check counts a unit field as one payload element, so
        // the seed is [Int(disc), PhantomData], never [Int(disc)] alone).
        let mut seed = Vec::with_capacity(1 + field_tys.len());
        seed.push(Constant::Int(disc));
        for fty in &field_tys {
            match self.seed_constant_ty(fty, 0) {
                Some(c) => seed.push(c),
                None => {
                    self.unsupported.push((format!("{span:?}"), "EnumCtor(non-scalar field seed)"));
                    return None;
                }
            }
        }
        let mut agg = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: enum_ty.clone(), value: Constant::Aggregate(seed) })
                .with_result(agg),
        );
        // Insert each payload value over the seed at its positional slot (1 + field
        // index). A unit slot has no value — its PhantomData seed IS the final value.
        for (i, val) in field_vals.iter().enumerate() {
            let Some(val) = val else { continue };
            let next = self.fresh();
            self.push_node(InstrNode::new(Inst::InsertField {
                    ty: enum_ty.clone(),
                    aggregate: agg,
                    field: (1 + i) as u32,
                    value: *val,
                })
                .with_result(next),
            );
            agg = next;
        }
        Some(agg)
    }

    /// Lower `if cond { then } [else { else }]` into a real CFG:
    ///
    /// ```text
    ///   cur:      <cond …>  cond_br %c -> then_blk, else_blk
    ///   then_blk: <then …>  br join(%t)        (omitted if then diverged)
    ///   else_blk: <else …>  br join(%e)        (omitted if else diverged)
    ///   join:     (params: [%r : T] if value-producing, else [])  <continues>
    /// ```
    ///
    /// Returns `Some(%r)` if the if produces a value (mapped result `Ty` != Unit), else `None`. If
    /// BOTH arms diverge the join is unreachable: leave the function sealed and return `None`.
    fn lower_if(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        cond: ExprId,
        then: ExprId,
        else_opt: Option<ExprId>,
    ) -> Option<ValueId> {
        // 1. Condition into the current (predecessor) block.
        let cond_val = match self.lower_expr(cond) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "If(cond unsupported)"));
                return None;
            }
        };
        self.lower_if_value(result_rty, span, cond_val, then, else_opt)
    }

    /// Trust (wave-DR): [`lower_if`] from an ALREADY-LOWERED condition value — the
    /// CFG half (arms, deferred `Br`s, SSA join merge) factored out so the `for`
    /// desugar's inner match (`lower_for_desugar_inner`, whose condition is the
    /// opaque variant test `lower_let_opaque_test` emits) rides the identical
    /// machinery. Behavior for `lower_if` callers is unchanged (pure refactor).
    fn lower_if_value(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        cond_val: ValueId,
        then: ExprId,
        else_opt: Option<ExprId>,
    ) -> Option<ValueId> {
        // 2. Join shape from the result type. The interpreter cannot materialize a `Ty::Unit` value,
        //    so a unit-typed `if` uses a zero-param join; a non-Unit result gets one join param.
        let result_ty = self.map_ty(result_rty);
        let value_producing = !matches!(result_ty, Ty::Unit);

        // 3. Allocate the three successor blocks.
        let then_id = self.fresh_block_id();
        let else_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // 4. Seal the predecessor with the conditional branch (arms take no incoming params — the
        //    join-incoming args are carried on each ARM's `Br` to the join, set in step 7).
        self.seal_with(Inst::CondBr {
            cond: cond_val,
            then_target: then_id,
            then_args: vec![],
            else_target: else_id,
            else_args: vec![],
        });

        // SSA-merge of mutable locals across the if. Snapshot the binding environment at the split:
        // any local a *reaching* arm rebinds to a different value needs a join block-param so a use
        // after the if sees the merged version (`map[local]` is reset to that param in step 8). We
        // lower each arm into its block but DEFER sealing its `Br`, capturing the arm's open cursor +
        // post-arm `locals` snapshot; once both arms are lowered we know the full merged-local set and
        // can seal each arm's `Br` with the result value + every merged local's per-arm value (so all
        // predecessors pass args of matching arity/order, as the interpreter's block-param bind needs).
        let pre_locals = self.locals.clone();

        // 5. THEN arm — lower body, then capture (do not seal yet).
        self.start_block(then_id, vec![]);
        let then_val = self.lower_expr(then);
        let then_arm = self.capture_arm(span, value_producing, then_val, "If(then no value)");

        // Restore the pre-split environment so the ELSE arm is lowered against the SAME bindings the
        // THEN arm started from (the THEN arm's pushes must not leak into the ELSE arm).
        self.locals = pre_locals.clone();

        // 6. ELSE arm.
        let else_arm = match else_opt {
            Some(else_expr) => {
                self.start_block(else_id, vec![]);
                let else_val = self.lower_expr(else_expr);
                self.capture_arm(span, value_producing, else_val, "If(else no value)")
            }
            None => {
                // No-else `if` is unit-typed (value_producing == false). The implicit else is an empty
                // block that falls straight through to the join carrying the PRE-SPLIT local values.
                self.start_block(else_id, vec![]);
                CapturedArm::reaching(self.snapshot_open(), pre_locals.clone())
            }
        };

        // 7. Merge. If neither arm reaches the join it is unreachable: leave sealed, return None.
        let then_reaches = then_arm.is_reaching();
        let else_reaches = else_arm.is_reaching();
        if !then_reaches && !else_reaches {
            // Seal any arm that DID reach (so its block is not left dangling-open) as Unreachable —
            // but here neither reaches, so both were already sealed by `capture_arm`. Nothing to do.
            return None;
        }

        // Locals merged at the join: those whose value in a reaching arm differs from the pre-split
        // value. (A local only one arm touches still differs in that arm vs the other arm's pre-split
        // value, so it is correctly included — every reaching predecessor passes its own version.)
        let merged: Vec<(LocalVarId, Ty)> =
            self.merged_locals(&pre_locals, &[&then_arm, &else_arm]);

        // Trust (wave-SEAM): the value-lane check must read the arm results BEFORE
        // `seal_arm_into_join` consumes the captured arms. A join over an opaque-lane
        // `Option` (flag-mapped `Ty::Bool` — the real seam's
        // `let evicted = if <cap> { self.ring.pop_front() } else { None };`) yields a
        // PROVEN discriminant iff EVERY reaching arm's result is itself ledgered (the
        // ctor const / a local-callee return / a nested proven join). An unproven arm
        // (an extern-call result, a merged unknown) simply leaves the join param
        // unledgered — no tag, no abort: the downstream value-lane consumer
        // (`lower_let_opaque_test`) fails closed on it and the pre-wave paths apply.
        let arms_all_lane = option_flag_lanes_enabled()
            && [&then_arm, &else_arm].iter().all(|arm| match arm {
                CapturedArm::Reaching { result: Some(v), .. } => {
                    self.option_lane_values.contains(v)
                }
                CapturedArm::Reaching { result: None, .. } => false,
                CapturedArm::Diverged => true, // no predecessor edge — vacuous
            })
            && matches!(result_rty.kind(), ty::Adt(a, _)
                if self.tcx.get_diagnostic_item(rustc_span::sym::Option) == Some(a.did()))
            && self.is_opaque_lane_enum(result_rty);
        // The join's result value id (only when value-producing) followed by one param per merged
        // local, in a fixed order shared by every predecessor's `Br` args.
        let result_param = if value_producing { Some(self.fresh()) } else { None };
        if arms_all_lane {
            if let Some(r) = result_param {
                self.option_lane_values.push(r);
            }
        }
        let merged_params: Vec<(ValueId, Ty)> =
            merged.iter().map(|(_, ty)| (self.fresh(), ty.clone())).collect();

        // 8a. Seal each reaching arm's deferred `Br`, passing [result?] ++ [merged-local values].
        self.seal_arm_into_join(then_arm, join_id, result_param.is_some(), &pre_locals, &merged);
        self.seal_arm_into_join(else_arm, join_id, result_param.is_some(), &pre_locals, &merged);

        // 8b. Open the join with [result?] ++ merged-local params; rebind each merged local to its
        //     new join param so a use after the if sees the merged value.
        let mut join_params: Vec<(ValueId, Ty)> = Vec::new();
        if let Some(r) = result_param {
            join_params.push((r, result_ty));
        }
        join_params.extend(merged_params.iter().cloned());
        // Restore to the pre-split environment, then layer the merged-local rebinds on top.
        self.locals = pre_locals;
        self.start_block(join_id, join_params);
        for ((var, ty), (param, _)) in merged.iter().zip(merged_params.iter()) {
            self.set_local(*var, *param, ty.clone());
        }
        result_param
    }

    /// Trust: snapshot the currently-open block's cursor (id + params + body) WITHOUT sealing it, so a
    /// branch terminator can be appended later once cross-arm merge args are known. Used by the
    /// deferred-`Br` arm machinery in `lower_if`, `lower_match`, and `lower_enum_match`.
    fn snapshot_open(&mut self) -> OpenBlock {
        OpenBlock {
            id: self.cur_id,
            params: std::mem::take(&mut self.cur_params),
            body: std::mem::take(&mut self.cur),
        }
    }

    /// Trust: capture an if/match arm's outcome after its body was lowered into the now-open block.
    /// Mirrors the per-arm value-hole handling the old inline code did: a DIVERGED arm (sealed by a
    /// `return`) is `Diverged`; a value-producing arm that yielded NO value is sealed `Unreachable`
    /// here (malformed-IR guard) and recorded `Reject`; otherwise the open block is snapshotted as
    /// `Reaching` for a deferred `Br`.
    fn capture_arm(
        &mut self,
        span: rustc_span::Span,
        value_producing: bool,
        arm_val: Option<ValueId>,
        no_value_label: &'static str,
    ) -> CapturedArm {
        if self.sealed {
            // Arm diverged (e.g. `return`); it does not reach the join.
            return CapturedArm::Diverged;
        }
        match (value_producing, arm_val) {
            (true, Some(v)) => CapturedArm::Reaching {
                open: self.snapshot_open(),
                locals: self.locals.clone(),
                result: Some(v),
            },
            (true, None) => {
                // Value-producing arm with no value (unsupported shape inside). Routing a 0-arg `Br`
                // to the result-param join would be an arity mismatch; seal `Unreachable` (the
                // `unsupported` push keeps the gate red so this module is never interpreted).
                self.unsupported.push((format!("{span:?}"), no_value_label));
                self.seal_with(Inst::Unreachable);
                CapturedArm::Diverged
            }
            (false, _) => CapturedArm::Reaching {
                open: self.snapshot_open(),
                locals: self.locals.clone(),
                result: None,
            },
        }
    }

    /// Trust: the set of locals (with their `Ty`) that need a join block-param: those bound in
    /// `pre_locals` whose value differs from the pre-split version in at least one REACHING arm.
    /// Order is stable (first appearance in `pre_locals`) so every predecessor's `Br` passes args in
    /// the same order as the join's params. A local with no recorded `Ty` is skipped (cannot type its
    /// param) — fail-safe: the merge just won't propagate it, which only loses precision, never
    /// produces malformed IR.
    fn merged_locals(
        &self,
        pre_locals: &[(LocalVarId, ValueId)],
        arms: &[&CapturedArm],
    ) -> Vec<(LocalVarId, Ty)> {
        // Distinct locals in pre-split order (last-write-wins value is the pre-split version).
        let mut seen: Vec<LocalVarId> = Vec::new();
        for (var, _) in pre_locals {
            if !seen.contains(var) {
                seen.push(*var);
            }
        }
        let mut out: Vec<(LocalVarId, Ty)> = Vec::new();
        for var in seen {
            let pre = last_value(pre_locals, var);
            let changed = arms.iter().any(|arm| match arm.locals() {
                Some(arm_locals) => last_value(arm_locals, var) != pre,
                None => false, // diverged arm contributes no predecessor, so ignore it
            });
            if changed {
                if let Some(ty) = self.local_ty(var) {
                    out.push((var, ty));
                }
            }
        }
        out
    }

    /// Trust: seal one captured arm's `Br` into the join, passing [result?] ++ each merged local's
    /// value in THIS arm (its post-arm value, or the pre-split value if the arm never touched it). A
    /// `Diverged` arm contributes nothing (already sealed). Restores the arm's open cursor first so
    /// `seal_with` finalizes the right block.
    fn seal_arm_into_join(
        &mut self,
        arm: CapturedArm,
        join_id: BlockId,
        has_result: bool,
        pre_locals: &[(LocalVarId, ValueId)],
        merged: &[(LocalVarId, Ty)],
    ) {
        let (open, locals, result) = match arm {
            CapturedArm::Reaching { open, locals, result } => (open, locals, result),
            CapturedArm::Diverged => return,
        };
        // Re-open this arm's block as the current cursor so `seal_with` finalizes it.
        self.cur_id = open.id;
        self.cur_params = open.params;
        self.cur = open.body;
        self.sealed = false;
        let mut args: Vec<ValueId> = Vec::new();
        if has_result {
            // A reaching value-producing arm always carries `Some(result)` (the no-value case became
            // `Diverged`). Defensive: skip if somehow absent rather than emit a bad arity.
            if let Some(r) = result {
                args.push(r);
            }
        }
        for (var, _) in merged {
            // This arm's value for the local: its post-arm version if it touched it, else pre-split.
            let v = last_value(&locals, *var).or_else(|| last_value(pre_locals, *var));
            if let Some(v) = v {
                args.push(v);
            }
        }
        self.seal_with(Inst::Br { target: join_id, args });
    }

    /// Lower `lhs && rhs` / `lhs || rhs` (`ExprKind::LogicalOp`) into the SAME short-circuiting CFG
    /// rustc's MIR builder emits for these operators (`expr/into.rs::LogicalOp`):
    ///
    /// ```text
    ///   &&:   a && b  ≡  if a { b } else { false }
    ///   ||:   a || b  ≡  if a { true } else { b }
    /// ```
    ///
    /// We do NOT route through `lower_if` because one arm is a *constant* (`true`/`false`), not a THIR
    /// `ExprId`; instead we replicate `lower_if`'s block plumbing directly. The result is always
    /// `bool` (so always value-producing — there is no unit/diverging case to special-case), and the
    /// arms merge through a single `Bool` join block-param — trust-ir's idiomatic SSA-with-block-param
    /// merge, exactly what the interpreter's `bind_block_params` consumes (no phi nodes). Matching
    /// MIR's structure here is what lets the differential oracle reach `mode = Agreed`.
    fn lower_logical_op(
        &mut self,
        span: rustc_span::Span,
        op: LogicalOp,
        lhs: ExprId,
        rhs: ExprId,
    ) -> Option<ValueId> {
        // 1. Evaluate the lazily-evaluated LHS (the branch condition) in the current block.
        let cond_val = match self.lower_expr(lhs) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "LogicalOp(lhs unsupported)"));
                return None;
            }
        };

        // 2. Three successors: the RHS-continuation arm, the short-circuit (constant) arm, and the
        //    Bool join. `&&` continues on `true` / short-circuits to `false`; `||` continues on
        //    `false` / short-circuits to `true`.
        let (constant, cond_true_is_rhs) = match op {
            LogicalOp::And => (false, true),
            LogicalOp::Or => (true, false),
        };
        let rhs_id = self.fresh_block_id();
        let short_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // CondBr: the arm taken when the condition is TRUE goes to `then_target`. For `&&` that's the
        // RHS arm; for `||` that's the short-circuit (`true`) arm.
        let (then_target, else_target) =
            if cond_true_is_rhs { (rhs_id, short_id) } else { (short_id, rhs_id) };
        self.seal_with(Inst::CondBr {
            cond: cond_val,
            then_target,
            then_args: vec![],
            else_target,
            else_args: vec![],
        });

        // The Bool result merged at the join.
        let join_param = self.fresh();

        // 3. RHS-continuation arm: evaluate `rhs`, branch its value to the join.
        self.start_block(rhs_id, vec![]);
        let rhs_val = self.lower_expr(rhs);
        let mut rhs_reaches_join = !self.sealed;
        if rhs_reaches_join {
            match rhs_val {
                Some(v) => self.seal_with(Inst::Br { target: join_id, args: vec![v] }),
                None => {
                    // RHS yielded no value (some unsupported shape inside it). Routing a 0-arg `Br`
                    // to the 1-param join would be a block-param arity mismatch (malformed IR), so
                    // seal `Unreachable`; `unsupported` already keeps the gate red.
                    self.unsupported.push((format!("{span:?}"), "LogicalOp(rhs no value)"));
                    self.seal_with(Inst::Unreachable);
                    rhs_reaches_join = false;
                }
            }
        }

        // 4. Short-circuit arm: emit the constant `true`/`false`, branch it to the join.
        self.start_block(short_id, vec![]);
        let const_val = self.fresh();
        self.push_node(InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(constant) })
                .with_result(const_val),
        );
        self.seal_with(Inst::Br { target: join_id, args: vec![const_val] });

        // 5. Join. The short-circuit arm always reaches it; if the RHS arm also failed to, the join is
        //    still reachable (via the constant arm), so always open it with the Bool param.
        let _ = rhs_reaches_join;
        self.start_block(join_id, vec![(join_param, Ty::Bool)]);
        Some(join_param)
    }

    /// Trust: lower the `?`-OPERATOR `x?` on a concrete `Result<T,E>` / `Option<T>` operand, in a fn
    /// returning the SAME enum family (the IDENTITY case — operand error/None type == fn return
    /// error/None type, no `From`-conversion). The `?` desugars (in HIR, recognized via
    /// `MatchSource::TryDesugar`) to
    ///
    /// ```text
    ///   match Try::branch(x) {
    ///       ControlFlow::Continue(v)        => v,
    ///       ControlFlow::Break(residual)    => return Try::from_residual(residual),
    ///   }
    /// ```
    ///
    /// `Try::branch` / `from_residual` are TRAIT METHODS the producer cannot resolve to a concrete
    /// `FuncId`, and `ControlFlow<Residual, Output>` is a heterogeneous, non-scalar-payload enum the
    /// `(tag,payload)` model declines — so the generic call/enum machinery fails closed. We BYPASS the
    /// desugar entirely and emit the semantically-equivalent CFG directly from the ORIGINAL operand:
    ///
    /// ```text
    ///   cur:    <x …>  %tag = ExtractField %x .0   %pl = ExtractField %x .1
    ///                  switch %tag -> default=err_blk, cases=[<Ok/Some discr> -> ok_blk]
    ///   ok_blk: br join(%pl)                                  ; Ok(v)/Some(v) → the ? value is v
    ///   err_blk: <build Err(%pl) / None>  return <that enum>  ; early-return the residual
    ///   join:   (params: [%r : <payload>])  <continues>
    /// ```
    ///
    /// SOUNDNESS of the identity bypass: `from_residual` on the identity impl (`E: From<E>` is the
    /// reflexive `From`, `Option`'s residual is the niladic `None`) is the IDENTITY on the error/None
    /// carrier — `Err(e)` stays `Err(e)`, `None` stays `None`. So reconstructing the return enum's
    /// Err/None variant directly from the operand's payload is exactly what `from_residual` computes.
    ///
    /// FAIL-CLOSED (the boundary — reported, never mis-lowered):
    ///   * the operand is not a concrete `Result`/`Option` enum, or its `(tag,payload)` repr is declined
    ///     (non-scalar / heterogeneous payload) by `register_enum`;
    ///   * the fn return type is not the SAME enum (a different `Result`/`Option`, or a non-enum) —
    ///     i.e. a `From`-CONVERTING `?` (`E -> E2`) which genuinely needs the `from_residual` trait call;
    ///   * the operand/return payload (Ok/Some) or error (Err) types are non-scalar, or the operand
    ///     itself does not lower (its own `unsupported` is recorded).
    fn lower_try_question(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
    ) -> Option<ValueId> {
        // 1. The desugar's scrutinee is `Try::branch(operand)`. Peel Scope/Use, then read the single
        //    call argument as the original operand `x`. Anything else (a hand-written match wearing the
        //    TryDesugar source — impossible from `?`, but guard) fails closed.
        let operand = match self.try_branch_operand(scrutinee) {
            Some(o) => o,
            None => {
                self.unsupported.push((format!("{span:?}"), "Try(branch operand not found)"));
                return None;
            }
        };

        // 2. The operand must be a concrete `Result<T,E>` / `Option<T>` enum whose `(tag,payload)` repr
        //    the enum model accepts (scalar, homogeneous payload). `Result<i32,i32>`/`Option<i32>` do;
        //    `Result<i32, String>` (non-scalar Err) does not.
        let operand_rty = self.thir.exprs[operand].ty;
        let (op_adt, op_args) = match operand_rty.kind() {
            ty::Adt(adt, args) if adt.is_enum() => (*adt, *args),
            _ => {
                self.unsupported.push((format!("{span:?}"), "Try(operand not an enum)"));
                return None;
            }
        };

        // 3. The fn return type must be the SAME enum family (identity case). A different enum is a
        //    `From`-converting `?` that needs the `from_residual` trait call we cannot lower.
        let ret_rty = match self.fn_return_rty {
            Some(t) => t,
            None => {
                self.unsupported.push((format!("{span:?}"), "Try(no fn return type)"));
                return None;
            }
        };
        let (ret_adt, ret_args) = match ret_rty.kind() {
            ty::Adt(adt, args) if adt.is_enum() => (*adt, *args),
            _ => {
                self.unsupported.push((format!("{span:?}"), "Try(fn return not an enum)"));
                return None;
            }
        };
        // Same enum DEFINITION. For `Result` the error type must also match (identity `From`); for
        // `Option` the residual is niladic so only the def needs to match. We require the operand and
        // return to be the SAME monomorphized enum type for `Result` (so `Err(e)` reconstructs with the
        // right error type), and the SAME def for `Option`. The simplest sound check that covers both:
        // identical `AdtDef` AND identical error/None carrier. We compare the discriminant-bearing repr
        // and the error payload type below; first require the same def.
        if op_adt.did() != ret_adt.did() {
            self.unsupported.push((format!("{span:?}"), "Try(operand/return enum differ)"));
            return None;
        }
        // Trust (B3-2c T2): the `?` lane is first-class-only. Both operand and
        // return must map to `Ty::Enum`; an opaque or mixed spelling fails closed.
        let op_spell = self.map_ty(operand_rty);
        let ret_spell = self.map_ty(ret_rty);
        match (&op_spell, &ret_spell) {
            (Ty::Enum(op_eid), Ty::Enum(ret_eid)) => {
                let (op_eid, ret_eid) = (*op_eid, *ret_eid);
                self.lower_try_question_general(
                    result_rty, span, operand, op_adt, op_args, ret_adt, ret_args, op_eid, ret_eid,
                )
            }
            (Ty::Enum(_), _) | (_, Ty::Enum(_)) => {
                self.unsupported.push((format!("{span:?}"), "Try(mixed enum spelling)"));
                None
            }
            _ => {
                self.unsupported.push((format!("{span:?}"), "Try(operand opaque lane)"));
                None
            }
        }
    }

    /// Trust (B3-2b/B3-2c): lower identity `?` when both the operand and the
    /// enclosing fn's return map to `Ty::Enum`. Load-bearing properties:
    ///   * the tag reads at the REGISTERED def's canonical repr (U8/I32…, never
    ///     blindly I64 — the interpreter's ExtractField type check is exact);
    ///   * the Switch case is the EFFECTIVE (sign-extended) Ok discriminant from
    ///     `effective_discriminants`, not rustc's raw truncated `Discr.val`;
    ///   * the payload extracts PER-ARM (ok slot 1 at the Ok variant's own field ty,
    ///     err slot 1 at the Err variant's) — slot 1 is typed by
    ///     the ACTIVE variant, so a shared pre-Switch extract would trap on
    ///     heterogeneous Result<T,E>;
    ///   * the residual reconstructs via the general ctor convention
    ///     (Const{Enum, Aggregate([Int(disc), seeds…])} + InsertField at slot 1).
    /// Identity guards (same def, residual arity +
    /// field-type equality — a From-converting `?` fails closed) run here.
    #[allow(clippy::too_many_arguments)]
    fn lower_try_question_general(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        operand: ExprId,
        op_adt: ty::AdtDef<'tcx>,
        op_args: ty::GenericArgsRef<'tcx>,
        ret_adt: ty::AdtDef<'tcx>,
        ret_args: ty::GenericArgsRef<'tcx>,
        op_eid: trust_ir::EnumId,
        ret_eid: trust_ir::EnumId,
    ) -> Option<ValueId> {
        // Same monomorphized enum on both sides — the identity-`?` case. Distinct
        // EnumIds mean distinct (DefId, args) registrations; reconstructing the
        // residual across them is the From-converting case → fail closed.
        if op_eid != ret_eid {
            self.unsupported.push((format!("{span:?}"), "Try(operand/return enum ids differ)"));
            return None;
        }
        let (ok_variant, err_variant) = match self.classify_try_variants(op_adt) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Try(cannot classify variants)"));
                return None;
            }
        };
        // Residual identity guard (mirrors the legacy body verbatim).
        let op_err_variant_def = op_adt.variant(err_variant);
        let ret_err_variant_def = ret_adt.variant(err_variant);
        if op_err_variant_def.fields.len() != ret_err_variant_def.fields.len() {
            self.unsupported.push((format!("{span:?}"), "Try(residual variant arity differs)"));
            return None;
        }
        if op_err_variant_def.fields.len() == 1 {
            let op_err_fty =
                op_err_variant_def.fields[rustc_abi::FieldIdx::ZERO].ty(self.tcx, op_args);
            let ret_err_fty =
                ret_err_variant_def.fields[rustc_abi::FieldIdx::ZERO].ty(self.tcx, ret_args);
            if op_err_fty != ret_err_fty {
                self.unsupported.push((format!("{span:?}"), "Try(From-converting residual)"));
                return None;
            }
        }
        // Registered-def facts, cloned out before any &mut self op.
        let (tag_ty, ok_disc, err_disc, ok_field_ty, err_field_ty, err_seed) = {
            let Some(def) = self.registered_enum(op_eid) else {
                self.unsupported.push((format!("{span:?}"), "Try(enum not registered)"));
                return None;
            };
            let Some(tag_ty) = def.canonical_tag_repr().map(|r| r.ty()) else {
                self.unsupported.push((format!("{span:?}"), "Try(no canonical tag)"));
                return None;
            };
            let Some(discs) = def.effective_discriminants() else {
                self.unsupported.push((format!("{span:?}"), "Try(discriminants unresolvable)"));
                return None;
            };
            let (Some(&ok_disc), Some(&err_disc)) =
                (discs.get(ok_variant.as_usize()), discs.get(err_variant.as_usize()))
            else {
                self.unsupported.push((format!("{span:?}"), "Try(variant/disc desync)"));
                return None;
            };
            let ok_field_ty = match def.variants.get(ok_variant.as_usize()).map(|v| &v.fields[..]) {
                Some([f]) => f.clone(),
                _ => {
                    self.unsupported.push((format!("{span:?}"), "Try(ok variant not 1-field)"));
                    return None;
                }
            };
            let err_fields = match def.variants.get(err_variant.as_usize()) {
                Some(v) => v.fields.clone(),
                None => {
                    self.unsupported.push((format!("{span:?}"), "Try(variant/disc desync)"));
                    return None;
                }
            };
            let (err_field_ty, err_seed) = match &err_fields[..] {
                [] => (None, None),
                [f] => match seed_constant(f) {
                    Some(seed) => (Some(f.clone()), Some(seed)),
                    None => {
                        self.unsupported.push((format!("{span:?}"), "Try(err field not seedable)"));
                        return None;
                    }
                },
                _ => {
                    self.unsupported.push((format!("{span:?}"), "Try(err variant multi-field)"));
                    return None;
                }
            };
            (tag_ty, ok_disc, err_disc, ok_field_ty, err_field_ty, err_seed)
        };
        // The `?`-result must be the Ok variant's own field type (defensive — the
        // classify step already keys on it) and scalar (the 2b payload scope).
        let result_ty = self.map_ty(result_rty);
        if !is_scalar_ty(&result_ty) {
            self.unsupported.push((format!("{span:?}"), "Try(non-scalar success payload)"));
            return None;
        }
        if ok_field_ty != result_ty {
            self.unsupported.push((format!("{span:?}"), "Try(payload slot != success type)"));
            return None;
        }

        let op_val = match self.lower_expr(operand) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Try(operand unsupported)"));
                return None;
            }
        };
        if self.is_borrow_ptr(op_val) {
            self.unsupported.push((format!("{span:?}"), "Try(operand is borrow ptr)"));
            return None;
        }
        let tag_val = self.fresh();
        self.push_node(InstrNode::new(Inst::ExtractField { ty: tag_ty.clone(), aggregate: op_val, field: 0 })
                .with_result(tag_val),
        );

        let ok_id = self.fresh_block_id();
        let err_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();
        self.seal_with(Inst::Switch {
            value: tag_val,
            default: err_id,
            default_args: vec![],
            cases: vec![SwitchCase { value: Constant::Int(ok_disc), target: ok_id, args: vec![] }],
            exhaustive_enum_unreachable: false,
        });
        let join_param = self.fresh();

        // Ok/Some arm: extract the payload AT THE OK VARIANT'S TYPE inside the arm
        // (slot 1 is typed by the active variant) and branch it to the join.
        self.start_block(ok_id, vec![]);
        let ok_payload = self.fresh();
        self.push_node(InstrNode::new(Inst::ExtractField {
                ty: ok_field_ty.clone(),
                aggregate: op_val,
                field: 1,
            })
            .with_result(ok_payload),
        );
        self.seal_with(Inst::Br { target: join_id, args: vec![ok_payload] });

        // Err/None arm: reconstruct the return enum's residual variant via the
        // general ctor convention and Return it.
        self.start_block(err_id, vec![]);
        let mut seeds = vec![Constant::Int(err_disc)];
        if let Some(seed) = err_seed.clone() {
            seeds.push(seed);
        }
        let err_const = self.fresh();
        self.push_node(InstrNode::new(Inst::Const {
                ty: Ty::Enum(ret_eid),
                value: Constant::Aggregate(seeds),
            })
            .with_result(err_const),
        );
        let err_enum = if let Some(err_fty) = err_field_ty {
            let err_payload = self.fresh();
            self.push_node(InstrNode::new(Inst::ExtractField { ty: err_fty, aggregate: op_val, field: 1 })
                    .with_result(err_payload),
            );
            let filled = self.fresh();
            self.push_node(InstrNode::new(Inst::InsertField {
                    ty: Ty::Enum(ret_eid),
                    aggregate: err_const,
                    field: 1,
                    value: err_payload,
                })
                .with_result(filled),
            );
            filled
        } else {
            err_const
        };
        self.seal_with(Inst::Return { values: vec![err_enum] });

        self.start_block(join_id, vec![(join_param, result_ty)]);
        Some(join_param)
    }

    /// Trust: peel `Scope`/`Use` wrappers off the `?`-desugar scrutinee and, if it is the expected
    /// `Try::branch(operand)` call, return the single argument `operand` ExprId. `None` for any other
    /// shape (defensive — `?` always produces this call).
    fn try_branch_operand(&self, mut scrutinee: ExprId) -> Option<ExprId> {
        loop {
            match &self.thir.exprs[scrutinee].kind {
                ExprKind::Scope { value, .. } => scrutinee = *value,
                ExprKind::Use { source } => scrutinee = *source,
                ExprKind::Call { args, .. } if args.len() == 1 => return Some(args[0]),
                _ => return None,
            }
        }
    }

    /// Trust: on a `Result`/`Option` enum, return `(success_variant, residual_variant)` —
    /// `(Ok, Err)` / `(Some, None)`. Identified by VARIANT NAME (`Ok`/`Some` is the `?`-continue /
    /// success variant; `Err`/`None` is the `?`-break / residual variant). Name-based because for
    /// `Result<i32,i32>` BOTH variants carry the SAME payload type (i32), so a payload-type match
    /// cannot disambiguate them. `None` (fail-closed) for any enum that is not a 2-variant
    /// `Result`/`Option` — a user `Try` enum is out of scope (it needs the real trait machinery).
    fn classify_try_variants(
        &self,
        adt: ty::AdtDef<'tcx>,
    ) -> Option<(rustc_abi::VariantIdx, rustc_abi::VariantIdx)> {
        if adt.variants().len() != 2 {
            return None;
        }
        let mut ok: Option<rustc_abi::VariantIdx> = None;
        let mut err: Option<rustc_abi::VariantIdx> = None;
        for (idx, variant) in adt.variants().iter_enumerated() {
            match variant.name {
                n if n == rustc_span::sym::Ok || n == rustc_span::sym::Some => ok = Some(idx),
                n if n == rustc_span::sym::Err || n == rustc_span::sym::None => err = Some(idx),
                _ => return None, // not a Result/Option variant name — out of scope
            }
        }
        Some((ok?, err?))
    }

    /// Lower `match scrut { L0 => B0, L1 => B1, …, _ => Bd }` whose arms are ALL integer-literal
    /// patterns plus exactly one wildcard default, into a `trust_ir::Switch` + per-arm blocks + a
    /// block-parameter join (the same SSA-merge `lower_if`/`lower_logical_op` use — trust-ir merges
    /// values with BLOCK PARAMETERS, not phi nodes):
    ///
    /// ```text
    ///   cur:       <scrut …>  switch %s -> default=wild_blk,
    ///                                       cases=[L0 -> blk0, L1 -> blk1, …]
    ///   blk0:      <B0 …>     br join(%v0)        (Unreachable if B0 produced no value)
    ///   blk1:      <B1 …>     br join(%v1)
    ///   wild_blk:  <Bd …>     br join(%vd)
    ///   join:      (params: [%r : T] if value-producing, else [])  <continues>
    /// ```
    ///
    /// Also supports integer RANGE-pattern arms — `lo..=hi` / `lo..hi` / `n @ lo..=hi` — lowered as a
    /// synthesized fallthrough test `lo <= x (&&) x <(=) hi` (two `CondBr`s, like a guard), routed to
    /// the arm body on match and to the next fallthrough arm on miss.
    ///
    /// FAIL-CLOSED: a pattern that is NOT a bare integer/char-literal `PatKind::Constant`, a bounded
    /// integer range, or a (guarded) catch-all/binding (enum/struct/or/slice/deref, a GUARDED
    /// range, an OPEN-ended or char/float range, a non-range `@`-subpattern), a missing wildcard
    /// default, or a non-integer scrutinee → recorded `unsupported`, NO `Switch` emitted. (The
    /// scrutinee is lowered first so its `unsupported` shapes are still reported.) Non-integer
    /// scrutinees with their own lowering ROUTE AWAY first: simple enums → `lower_enum_match`,
    /// bool → `lower_bool_match` (a `CondBr`, the built-MIR bool-`SwitchInt` shape), tuples →
    /// `lower_tuple_match` (irrefutable single-arm destructure); first-class `Ty::Char` stays HERE
    /// with its unsigned 32-bit code-point carrier. A REF scrutinee with an int/char pointee stays HERE
    /// too, as the DEREF-MATCH: strip one `PatKind::Deref` layer per arm, `Load` the pointee from
    /// the registered borrow pointer, `Switch` on the loaded value. Any other non-integer
    /// scrutinee fails closed with the PRECISE `non_integer_scrut_tag` (float/str/slice/array/
    /// raw-ptr/generic-opaque/ref/union) — float deliberately so (match semantics ≠ int equality).
    ///
    /// Returns `Some(%r)` for a value-producing match, else `None`. If no arm reaches the join (every
    /// arm diverged), the join is unreachable: leave sealed, return `None`.
    fn lower_match(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: Vec<ArmId>,
    ) -> Option<ValueId> {
        // 0. The scrutinee must be an integer-shaped scalar (including first-class `Ty::Char`) we
        // can `Switch` on.
        let scrut_rty = self.thir.exprs[scrutinee].ty;
        // Trust: a SIMPLE-enum scrutinee (`match o { Some(x) => .., None => .. }`) routes to the
        // variant-aware match path: extract the `(tag, payload)` tuple's tag, `Switch` on the
        // discriminant, bind each arm's payload subpattern. The integer path below is unchanged.
        if matches!(scrut_rty.kind(), ty::Adt(adt, _) if adt.is_enum()) {
            return self.lower_enum_match(result_rty, span, scrutinee, &arms);
        }
        // Trust (wave-MR): a SHARED ref-to-enum scrutinee (`match r { V => .. }` on `r: &E`, both
        // the match-ergonomics and explicit `&V` arm forms) routes to the SAME variant-aware match
        // path — `lower_enum_match` peels the ref and reads the discriminant via a deref-`Load` of
        // the pointee enum value (the wave-11 aggregate-Load + wave-V discriminant `Switch`). A
        // `&mut E` / raw-ptr scrutinee is out of scope (shared-ref only, matching the deref-match
        // contract); payload-BINDING arms (by-ref ergonomic bindings) fail closed inside — this
        // first slice is discriminant-only.
        if matches!(scrut_rty.kind(),
            ty::Ref(_, pointee, m)
                if m.is_not() && matches!(pointee.kind(), ty::Adt(a, _) if a.is_enum()))
        {
            return self.lower_enum_match(result_rty, span, scrutinee, &arms);
        }
        // Trust: a BOOL scrutinee routes to the two-arm `CondBr` path — the exact shape built MIR
        // gives a bool `match` (`SwitchInt(b) -> [0: false-arm, otherwise: true-arm]`, i.e. the
        // `if` encoding), NOT a `Switch` with Bool case constants (the integer `Switch` below
        // compares integer constants (`Int`, or v24 `U128` for the upper half); a Bool selector is
        // a different constant domain).
        if scrut_rty.is_bool() {
            return self.lower_bool_match(result_rty, span, scrutinee, &arms);
        }
        // Trust: a TUPLE scrutinee routes to the irrefutable single-arm destructure path
        // (`match (a, b) { (x, y) => … }` — bindings via `ExtractField` on the already-modeled
        // tuple aggregate; straight-line, no dispatch). A STRUCT scrutinee
        // (`match p { P { x, y } => … }`, and the `let P { x, y } = p` desugar) is the SAME
        // `PatKind::Leaf` destructure over the first-class `Ty::Struct` aggregate — `sp.field`
        // carries declaration-order indices, exactly the aggregate's field order. Multi-arm
        // matches (literal element patterns) stay fail-closed there; unions are NOT `is_struct`
        // and keep the fail-closed fall-through below.
        // Trust (wave-AM): a FIXED-LENGTH ARRAY scrutinee (`match x { [a, b, c] => … }`) routes to
        // the SAME destructure path — map_ty lowers `[T; N]` (N>0) to `Ty::Tuple([T; N])`, so the
        // `ExtractField`-per-element machinery is identical to a tuple. The array-pattern arm form
        // (`PatKind::Array`) is normalized positionally in the classifier there; rest patterns
        // (`[a, .., c]`) and `[T; 0]` (mapped to `Ty::Array`, not `Ty::Tuple`) fall closed inside.
        if matches!(scrut_rty.kind(), ty::Tuple(_))
            || matches!(scrut_rty.kind(), ty::Adt(adt, _) if adt.is_struct())
            || matches!(scrut_rty.kind(), ty::Array(..))
        {
            return self.lower_tuple_match(result_rty, span, scrutinee, &arms);
        }
        // Trust: a REF scrutinee with an int/char POINTEE (`match &x { &0 => .. }`, `match r { .. }`
        // on `r: &i32` — explicit `&pat` arms and the match-ergonomics form both carry one outer
        // `PatKind::Deref` layer in THIR) routes through the DEREF-MATCH path: classification strips
        // that single layer per arm (below), and after the scrutinee lowers to a LEDGER-registered
        // borrow pointer one `Load` of the pointee feeds the ordinary integer `Switch` — exactly the
        // `ExprKind::Deref` contract (registered borrow pointers only, scalar pointees only). Every
        // other non-integer scrutinee stays FAIL-CLOSED with a PRECISE tag (`non_integer_scrut_tag`);
        // notably a FLOAT scrutinee (direct or behind `&`) is a SEMANTICS decision (NaN never
        // matches itself, `-0.0` matches `0.0`) and must never be lowered silently as int equality.
        let (eff_scrut_rty, deref_scrut) = match scrut_rty.kind() {
            ty::Ref(_, pointee, _)
                if matches!(pointee.kind(), ty::Int(_) | ty::Uint(_) | ty::Char) =>
            {
                (*pointee, true)
            }
            _ => (scrut_rty, false),
        };
        let scrut_signed = match eff_scrut_rty.kind() {
            ty::Int(_) => true,
            ty::Uint(_) => false,
            // Trust: `char` — an unsigned 32-bit code-point scalar (`map_ty` maps it to `Ty::U32`);
            // its literal patterns come through `const_pat_int`'s char arm in the same integer
            // constant domain the `Switch` compares. Char RANGE patterns stay fail-closed
            // in `range_pat_bounds` (`pr.ty` is char, not an int).
            ty::Char => false,
            _ => {
                self.unsupported.push((format!("{span:?}"), non_integer_scrut_tag(scrut_rty)));
                return None;
            }
        };
        let scrut_ty = self.map_ty(eff_scrut_rty);
        // `map_ty` fail-closes unmapped integer widths to `Unit`; guard against an i128-but-Unit hole.
        if !matches!(
            scrut_ty,
            Ty::I8
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
        ) {
            self.unsupported.push((format!("{span:?}"), "Match(unmapped scrutinee Ty)"));
            return None;
        }
        let scrut_bits = scrut_ty_bits(&scrut_ty);

        // 1. Classify arms WITHOUT mutating any IR state yet (so a fail-closed reject leaves the CFG
        //    untouched apart from the recorded `unsupported`). Collect (literal raw bits, body ExprId) for
        //    case arms and the single wildcard default body. Reject non-literal patterns, a missing
        //    default, or more than one default.
        //
        // Trust: a match-arm GUARD — `p if cond => body` — is lowered as a guard-test block inserted
        // BETWEEN the pattern dispatch and the body. After the pattern matches, the guard expr is
        // lowered to a bool and a `CondBr` routes guard-true → the arm body, guard-false → "the
        // remaining arms" (the fallthrough). A guard can READ the pattern's bindings, so they are bound
        // before the guard is evaluated. Supported here: a guard on an integer-literal `Constant` arm
        // (guard-false → the default arm, since no other literal can match the same scrutinee) and a
        // guard on a by-value WILDCARD or BINDING arm (a catch-all whose guard-false chains to the next
        // catch-all, ending at the plain default). Or-patterns, by-ref bindings, `@`-subpatterns, and
        // an arm with no reachable default behind a guard stay FAIL-CLOSED.
        //
        // Each arm is classified into an owned `ArmClass` (no `self` mutation while `arm` is borrowed
        // — mirrors `lower_stmt`'s snapshot pattern). `tcx` is `Copy`, so the const extraction reads it
        // without holding a `&self` borrow that conflicts with the later `unsupported.push`.
        enum ArmClass {
            // An integer-literal `Switch` case with an OPTIONAL guard (`L if g => body`).
            Case(u128, Option<ExprId>, ExprId),
            // A by-value WILDCARD or BINDING catch-all WITH a guard (`_ if g => body` / `n if g =>
            // body`). The optional `LocalVarId` binds the scrutinee value before the guard runs.
            GuardedCatchAll(Option<LocalVarId>, ExprId, ExprId),
            // Trust: a RANGE-pattern arm (`1..=5 => body` / `1..5 => body` / `n @ 1..=5 => body`). It
            // is a generalized guarded catch-all: instead of a `Switch` literal it carries a SYNTHESIZED
            // range check `lo <= x (&&) x <(=) hi` on the scrutinee, routed (like a guard) to its body
            // on match and to the fallthrough chain on miss. `(lo, hi, included)` are the integer bounds
            // (`included` = `..=`); the optional `LocalVarId` is the `n @` binding (bound to the
            // scrutinee before the body). FAIL-CLOSED ranges (open-ended, char/float, guarded) are
            // rejected at classification, so a `Range` here is always a bounded integer range.
            Range(u128, u128, bool, Option<LocalVarId>, ExprId),
            // The terminal (unguarded, irrefutable) catch-all default. `None` binding = a plain `_`;
            // `Some(var)` = a by-value binding arm `n => body` (Trust wave-Q), which binds the
            // scrutinee to `var` before the body — an irrefutable catch-all exactly like `_` but named.
            Wild(Option<LocalVarId>, ExprId),
            Reject(&'static str),
        }
        let tcx = self.tcx;
        let classes: Vec<ArmClass> = arms
            .iter()
            .map(|arm_id| {
                let arm = &self.thir.arms[*arm_id];
                let guard = arm.guard;
                // Trust: DEREF-MATCH arm normalization — strip the single `&`-layer
                // (`PatKind::Deref`, explicit `&pat` or match-ergonomics implicit) each non-wild
                // arm of a ref-scrutinee match carries; `_` matches the reference wholesale (no
                // deref, no adjustment) and passes through unchanged. A TOP-LEVEL binding would
                // bind the REFERENCE itself (a `Ty::Ptr` local — but the classified scrutinee
                // value below is the LOADED pointee, so binding it would be ill-typed) and any
                // other top-level kind means the pattern does not destructure through the ref —
                // both FAIL-CLOSED with precise tags. Pinned deref patterns (`&pin`) are not
                // modeled.
                let pat_kind: &PatKind<'tcx> = if deref_scrut {
                    match &arm.pattern.kind {
                        PatKind::Deref { pin: rustc_hir::Pinnedness::Not, subpattern } => {
                            &subpattern.kind
                        }
                        PatKind::Wild => &arm.pattern.kind,
                        PatKind::Binding { .. } => {
                            return ArmClass::Reject("Match(ref binding arm)");
                        }
                        _ => return ArmClass::Reject("Match(ref arm not a deref pattern)"),
                    }
                } else {
                    &arm.pattern.kind
                };
                match pat_kind {
                    PatKind::Wild => match guard {
                        None => ArmClass::Wild(None, arm.body),
                        Some(g) => ArmClass::GuardedCatchAll(None, g, arm.body),
                    },
                    // A by-value binding (`n`) is a catch-all that names the scrutinee. With a guard
                    // (`n if g`) it is a GUARDED fallthrough. Trust (wave-Q): an UNGUARDED by-value
                    // binding `n => body` is an IRREFUTABLE catch-all — the terminal default, binding
                    // the scrutinee to `n` before the body (`ArmClass::Wild(Some(var), ..)`), the
                    // exact `_`-default shape plus a named binding. Any arm AFTER it is unreachable
                    // (handled in the default-collection loop). A by-REF binding, an `@`-subpattern,
                    // or an or-pattern still fails closed on its own arm below.
                    PatKind::Binding {
                        var,
                        mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                        subpattern: None,
                        ..
                    } => match guard {
                        Some(g) => ArmClass::GuardedCatchAll(Some(*var), g, arm.body),
                        None => ArmClass::Wild(Some(*var), arm.body),
                    },
                    // Trust: a NAMED range binding `n @ 1..=5 => body`. The `@`-subpattern is a RANGE;
                    // `n` is bound to the scrutinee value before the body (the by-value catch-all
                    // binding). We model only an UNGUARDED by-value `n @ <range>` (a guarded one, a
                    // by-ref binding, or a non-range subpattern stays fail-closed).
                    PatKind::Binding {
                        var,
                        mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                        subpattern: Some(sub),
                        ..
                    } => match (&sub.kind, guard) {
                        (PatKind::Range(pr), None) => {
                            match range_pat_bounds(tcx, pr, scrut_signed, scrut_bits) {
                                Some((lo, hi, inc)) => {
                                    ArmClass::Range(lo, hi, inc, Some(*var), arm.body)
                                }
                                None => ArmClass::Reject("Match(unbounded/non-int range pattern)"),
                            }
                        }
                        (PatKind::Range(_), Some(_)) => {
                            ArmClass::Reject("Match(guarded range binding)")
                        }
                        _ => ArmClass::Reject("Match(non-range @-binding)"),
                    },
                    // Trust: a bare RANGE arm `1..=5 => body` / `1..5 => body`. Lowered as a synthesized
                    // range check on the scrutinee (a generalized guarded catch-all — see `ArmClass::
                    // Range`). A GUARDED range (`1..=5 if g`) stays fail-closed (the range-check + guard
                    // composition is a separate step). Open-ended/char/float ranges fail closed in
                    // `range_pat_bounds`.
                    PatKind::Range(pr) => match guard {
                        None => match range_pat_bounds(tcx, pr, scrut_signed, scrut_bits) {
                            Some((lo, hi, inc)) => ArmClass::Range(lo, hi, inc, None, arm.body),
                            None => ArmClass::Reject("Match(unbounded/non-int range pattern)"),
                        },
                        Some(_) => ArmClass::Reject("Match(guarded range pattern)"),
                    },
                    PatKind::Constant { value } => {
                        match const_pat_int(tcx, *value, scrut_signed, scrut_bits) {
                            Some(lit) => ArmClass::Case(lit, guard, arm.body),
                            None => ArmClass::Reject("Match(non-integer-literal pattern)"),
                        }
                    }
                    // enum/tuple/struct/by-ref-binding/or/slice/deref — not lowered yet.
                    _ => ArmClass::Reject("Match(unsupported pattern)"),
                }
            })
            .collect();

        // A `Case` carries (literal, optional-guard, body). A `GuardedCatchAll` carries (optional
        // binding, guard, body) and a `Range` carries (lo, hi, included, optional binding, body); BOTH
        // are FALLTHROUGH arms — reached from the `Switch` default, each routing its miss to the NEXT
        // fallthrough arm. They chain TOGETHER in source order (a literal followed by a range followed
        // by a guarded `_`, etc.), so a single ordered `fall_arms` list preserves their interleaving.
        // The plain `Wild` is the terminal default. Source order matters, so collect in order.
        // `Copy` (all fields are `Copy`) so the block-allocation `map` below can `match *fa` out by
        // value while `fall_arms` stays borrowed.
        #[derive(Clone, Copy)]
        enum FallArm {
            // A guarded catch-all `_ if g` / `n if g`: (optional binding, guard expr, body).
            Guarded(Option<LocalVarId>, ExprId, ExprId),
            // A range arm `lo..=hi` / `lo..hi` / `n @ lo..=hi`: (lo, hi, included, optional binding,
            // body). Its match test is a synthesized `lo <= x (&&) x <(=) hi`, not an expression.
            Range(u128, u128, bool, Option<LocalVarId>, ExprId),
        }
        let mut case_lits: Vec<(u128, Option<ExprId>, ExprId)> = Vec::new();
        let mut fall_arms: Vec<FallArm> = Vec::new();
        let mut default_body: Option<ExprId> = None;
        // Trust (wave-Q): the terminal default's optional by-value binding (`n => body` binds the
        // scrutinee to `n`); `None` for a plain `_` default.
        let mut default_bind: Option<LocalVarId> = None;
        let mut saw_default = false;
        for class in classes {
            match class {
                ArmClass::Reject(why) => {
                    self.unsupported.push((format!("{span:?}"), why));
                    return None;
                }
                ArmClass::Wild(bind, body) => {
                    // Trust (wave-Q): the FIRST irrefutable catch-all (a plain `_` OR an unguarded
                    // by-value binding `n`) is the terminal default. A SECOND irrefutable catch-all
                    // (e.g. a trailing `_` after a binding arm, which rustc keeps in the THIR when
                    // `unreachable_patterns` is not denied) is UNREACHABLE dead code: ignore it rather
                    // than reject. Sound — once the first irrefutable arm matches, nothing after it can
                    // execute, exactly as rustc's own match lowering treats it (the built MIR routes
                    // everything to the first catch-all; the derived body agrees).
                    if saw_default {
                        continue;
                    }
                    saw_default = true;
                    default_body = Some(body);
                    default_bind = bind;
                }
                ArmClass::GuardedCatchAll(b, g, body) => {
                    // A guarded catch-all AFTER the plain default would be unreachable (the default
                    // already matches everything). A well-typed match never produces that, but guard
                    // defensively.
                    if saw_default {
                        self.unsupported
                            .push((format!("{span:?}"), "Match(guarded arm after default)"));
                        return None;
                    }
                    fall_arms.push(FallArm::Guarded(b, g, body));
                }
                ArmClass::Range(lo, hi, inc, b, body) => {
                    // A range arm after the plain default would be unreachable too.
                    if saw_default {
                        self.unsupported
                            .push((format!("{span:?}"), "Match(range arm after default)"));
                        return None;
                    }
                    fall_arms.push(FallArm::Range(lo, hi, inc, b, body));
                }
                ArmClass::Case(lit, guard, body) => {
                    if saw_default {
                        self.unsupported
                            .push((format!("{span:?}"), "Match(case arm after default)"));
                        return None;
                    }
                    case_lits.push((lit, guard, body));
                }
            }
        }
        // An open integer type is non-exhaustive without a wildcard; a `match` that type-checked must
        // have one. If absent (e.g. a bool-like exhaustive match that slipped the type guard), fail
        // closed rather than emit a `Switch` with an unreachable-but-required default arm body. A
        // guarded catch-all is NOT a default (its guard can be false), so it never substitutes here.
        let default_body = match default_body {
            Some(b) => b,
            None => {
                self.unsupported.push((format!("{span:?}"), "Match(no wildcard default arm)"));
                return None;
            }
        };

        // 2. Lower the scrutinee value into the current (predecessor) block.
        let scrut_val = match self.lower_expr(scrutinee) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Match(scrutinee unsupported)"));
                return None;
            }
        };
        // Trust: DEREF-MATCH — the scrutinee is a REF; `Load` its int/char pointee ONCE and switch
        // on the loaded value. Only a LEDGER-registered borrow pointer may be loaded (the
        // `ExprKind::Deref` contract): one the `Borrow` arm produced, or a wave-5 ref-typed
        // scalar-pointee PARAM registered at binding. A raw/unregistered pointer fails closed
        // BEFORE any `Switch` is emitted.
        let scrut_val = if deref_scrut {
            if !self.is_borrow_ptr(scrut_val) {
                self.unsupported
                    .push((format!("{span:?}"), "Match(ref scrutinee not a registered borrow)"));
                return None;
            }
            let loaded = self.fresh();
            self.push_node(InstrNode::new(Inst::Load {
                    ty: scrut_ty.clone(),
                    ptr: scrut_val,
                    volatile: false,
                    align: None,
                })
                .with_result(loaded),
            );
            loaded
        } else {
            scrut_val
        };

        // 3. Join shape from the result type (mirrors `lower_if`): unit → zero-param join.
        let result_ty = self.map_ty(result_rty);
        let value_producing = !matches!(result_ty, Ty::Unit);

        // 4. Allocate the blocks. Each arm needs a BODY block; a guarded arm ALSO needs a guard-test
        //    block between its dispatch edge and its body. The plain default and the join are last.
        //
        //    `fallthrough` is the block a FAILED guard jumps to ("continue matching the remaining
        //    arms"). It is built bottom-up: the terminal fallthrough is the plain default; each guarded
        //    catch-all, walked in REVERSE source order, becomes the new fallthrough head (its
        //    guard-false routes to the previous fallthrough). A guarded literal `Case`'s guard-false
        //    also jumps to this chain head — a different literal can never match the same scrutinee, so
        //    once `x == L` fails its guard the only remaining candidates are the catch-alls/default.
        let default_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // 4a. Per literal case: (literal, guard-test-block-or-None, body-block, guard, body).
        struct CaseBlk {
            lit: u128,
            entry: BlockId, // the Switch case target (guard-test block if guarded, else body)
            body_blk: BlockId,
            guard: Option<ExprId>,
            body: ExprId,
        }
        let case_blocks: Vec<CaseBlk> = case_lits
            .iter()
            .map(|&(lit, guard, body)| {
                let body_blk = self.fresh_block_id();
                let entry = if guard.is_some() { self.fresh_block_id() } else { body_blk };
                CaseBlk { lit, entry, body_blk, guard, body }
            })
            .collect();

        // 4b. Per FALLTHROUGH arm (guarded catch-all OR range): a TEST block (where the arm's match
        //     condition is evaluated) + a body block. A guarded arm's test block lowers its guard expr;
        //     a range arm's test block evaluates `lo <= x`, then chains through a SECOND `hi_blk` test
        //     block (`x <(=) hi`). `entry` is the block the previous fallthrough (or the Switch default)
        //     jumps to to "try this arm" — the guard-test block, or the range's lo-check block.
        enum FallBlk {
            Guarded {
                binding: Option<LocalVarId>,
                guard_blk: BlockId,
                body_blk: BlockId,
                guard: ExprId,
                body: ExprId,
            },
            Range {
                lo: u128,
                hi: u128,
                included: bool,
                binding: Option<LocalVarId>,
                lo_blk: BlockId,
                hi_blk: BlockId,
                body_blk: BlockId,
                body: ExprId,
            },
        }
        impl FallBlk {
            /// The block the chain jumps to to TRY this arm (its first test block).
            fn entry(&self) -> BlockId {
                match self {
                    FallBlk::Guarded { guard_blk, .. } => *guard_blk,
                    FallBlk::Range { lo_blk, .. } => *lo_blk,
                }
            }
        }
        let fall_blocks: Vec<FallBlk> = fall_arms
            .iter()
            .map(|fa| match *fa {
                FallArm::Guarded(binding, guard, body) => FallBlk::Guarded {
                    binding,
                    guard_blk: self.fresh_block_id(),
                    body_blk: self.fresh_block_id(),
                    guard,
                    body,
                },
                FallArm::Range(lo, hi, included, binding, body) => FallBlk::Range {
                    lo,
                    hi,
                    included,
                    binding,
                    lo_blk: self.fresh_block_id(),
                    hi_blk: self.fresh_block_id(),
                    body_blk: self.fresh_block_id(),
                    body,
                },
            })
            .collect();

        // 4c. The fallthrough chain head: the FIRST fallthrough arm's entry (test) block, or the plain
        //     default if there are none.
        let chain_head = fall_blocks.first().map(|c| c.entry()).unwrap_or(default_id);

        // 5. Seal the predecessor with the `Switch`: each literal case targets its ENTRY block (a
        //    guard-test block when guarded, the body block otherwise); the default targets the
        //    fallthrough chain head.
        let cases: Vec<SwitchCase> = case_blocks
            .iter()
            .map(|c| SwitchCase {
                value: integer_constant_from_bits(c.lit, scrut_signed, scrut_bits),
                target: c.entry,
                args: vec![],
            })
            .collect();
        self.seal_with(Inst::Switch {
            value: scrut_val,
            default: chain_head,
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        });

        // 6. Lower every block. Same value-hole handling as before (a value-producing arm yielding
        //    no value seals `Unreachable`). A guard-test block lowers the guard expr (binding the
        //    pattern's local first, for a catch-all) and `CondBr`s true → body, false → next fallthrough.
        //
        // Trust: mutable-local merge across `match` arms — an arm BODY that reassigns an outer local
        // now merges through join block-params, the SAME deferred-`Br` machinery `lower_if` uses:
        // each arm body is lowered into its block but its `Br` to the join is DEFERRED (captured as a
        // `CapturedArm`); once every arm is lowered the full merged-local set is known and each
        // reaching arm's `Br` is sealed with [result?] ++ [its per-arm value of every merged local].
        // The env is snapshotted/restored around each arm so arms don't cross-contaminate; a
        // catch-all's pattern binding is a FRESH per-arm local (a new `LocalVarId`), so it never
        // enters the merge (only locals bound BEFORE the match do). A GUARD-test block that itself
        // reassigns a local stays FAIL-CLOSED: its successors are dispatch edges (body / next
        // fallthrough), not the join, so no param-merge path exists for it.
        let pre_locals = self.locals.clone();
        let mut captured: Vec<CapturedArm> = Vec::new();

        // 6a. Literal cases: optional guard-test block, then the body block.
        for c in &case_blocks {
            if let Some(g) = c.guard {
                // Guard-test block: evaluate the guard (no pattern binding — a literal binds nothing)
                // and route true → body, false → the fallthrough chain head.
                self.locals = pre_locals.clone();
                self.start_block(c.entry, vec![]);
                let gv = match self.lower_expr(g) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{span:?}"), "Match(case guard unsupported)"));
                        if !self.sealed {
                            self.seal_with(Inst::Unreachable);
                        }
                        continue;
                    }
                };
                self.seal_with(Inst::CondBr {
                    cond: gv,
                    then_target: c.body_blk,
                    then_args: vec![],
                    else_target: chain_head,
                    else_args: vec![],
                });
                if locals_changed(&pre_locals, &self.locals) {
                    self.unsupported.push((format!("{span:?}"), "Match(guard reassigns local)"));
                }
            }
            self.locals = pre_locals.clone();
            captured.push(self.lower_match_arm(
                span,
                value_producing,
                c.body_blk,
                c.body,
                "Match(case arm no value)",
            ));
        }

        // 6b. Fallthrough arms (guarded catch-alls AND range arms), in source order. Each arm's TEST
        //     block(s) route a MATCH → its body and a MISS → the NEXT fallthrough arm's entry block (or
        //     the plain default for the last one). The body block binds the pattern local (`n` / `n @`)
        //     to the scrutinee value first (a guard / the body may read it).
        for (i, c) in fall_blocks.iter().enumerate() {
            let next_fallthrough = fall_blocks.get(i + 1).map(|n| n.entry()).unwrap_or(default_id);
            match c {
                FallBlk::Guarded { binding, guard_blk, body_blk, guard, body } => {
                    self.locals = pre_locals.clone();
                    self.start_block(*guard_blk, vec![]);
                    // Bind the pattern's local (`n`) to the scrutinee SSA value before the guard runs
                    // (the guard may read it). The scrutinee value dominates this block, so the binding
                    // is just a local-map entry — no instruction. A `_` catch-all binds nothing.
                    if let Some(var) = binding {
                        self.set_local(*var, scrut_val, scrut_ty.clone());
                    }
                    let gv = match self.lower_expr(*guard) {
                        Some(v) => v,
                        None => {
                            self.unsupported
                                .push((format!("{span:?}"), "Match(catch-all guard unsupported)"));
                            if !self.sealed {
                                self.seal_with(Inst::Unreachable);
                            }
                            continue;
                        }
                    };
                    self.seal_with(Inst::CondBr {
                        cond: gv,
                        then_target: *body_blk,
                        then_args: vec![],
                        else_target: next_fallthrough,
                        else_args: vec![],
                    });
                    // A guard reassigning a local stays fail-closed (its successors are dispatch
                    // edges, not the join — no param-merge path). The pattern BINDING itself is a
                    // fresh local, invisible to `locals_changed` (it wasn't in `pre_locals`)…
                    // except that `set_local` above pushed it AFTER the snapshot, so compare
                    // against the env-with-binding: rebuild it for the check.
                    let mut guard_base = pre_locals.clone();
                    if let Some(var) = binding {
                        guard_base.push((*var, scrut_val));
                    }
                    if locals_changed(&guard_base, &self.locals) {
                        self.unsupported
                            .push((format!("{span:?}"), "Match(guard reassigns local)"));
                    }

                    // The catch-all's body block, with the same binding in scope. The binding is a
                    // FRESH per-arm local (never in `pre_locals`), so the join merge ignores it.
                    self.locals = pre_locals.clone();
                    if let Some(var) = binding {
                        self.set_local(*var, scrut_val, scrut_ty.clone());
                    }
                    captured.push(self.lower_match_arm(
                        span,
                        value_producing,
                        *body_blk,
                        *body,
                        "Match(catch-all arm no value)",
                    ));
                }
                // Trust: a RANGE arm — the synthesized test `lo <= x (&&) x <(=) hi`, emitted as TWO
                // CondBr blocks in sequence (a `BinOp::And` of two bools is a type error in the
                // interpreter — `eval_binop` `expect_int_value`s its operands — so we short-circuit
                // through control flow instead). `lo_blk`: `lo <= x` ? `hi_blk` : next-fallthrough.
                // `hi_blk`: `x <(=) hi` ? body : next-fallthrough. Both miss-edges go to the SAME next
                // fallthrough (a scrutinee outside the range continues matching the remaining arms).
                FallBlk::Range { lo, hi, included, binding, lo_blk, hi_blk, body_blk, body } => {
                    // Lower-bound test block: `lo <= x`.
                    self.locals = pre_locals.clone();
                    self.start_block(*lo_blk, vec![]);
                    let lo_c = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: scrut_ty.clone(),
                            value: integer_constant_from_bits(*lo, scrut_signed, scrut_bits),
                        })
                        .with_result(lo_c),
                    );
                    let lo_le = self.fresh();
                    let le_op = if scrut_signed { ICmpOp::Sle } else { ICmpOp::Ule };
                    self.push_node(InstrNode::new(Inst::ICmp {
                            op: le_op,
                            ty: scrut_ty.clone(),
                            lhs: lo_c,
                            rhs: scrut_val,
                        })
                        .with_result(lo_le),
                    );
                    self.seal_with(Inst::CondBr {
                        cond: lo_le,
                        then_target: *hi_blk,
                        then_args: vec![],
                        else_target: next_fallthrough,
                        else_args: vec![],
                    });

                    // Upper-bound test block: `x <(=) hi` (`<=` for `..=` Included, `<` for `..`).
                    self.locals = pre_locals.clone();
                    self.start_block(*hi_blk, vec![]);
                    let hi_c = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: scrut_ty.clone(),
                            value: integer_constant_from_bits(*hi, scrut_signed, scrut_bits),
                        })
                        .with_result(hi_c),
                    );
                    let hi_cmp = self.fresh();
                    let hi_op = match (*included, scrut_signed) {
                        (true, true) => ICmpOp::Sle,
                        (true, false) => ICmpOp::Ule,
                        (false, true) => ICmpOp::Slt,
                        (false, false) => ICmpOp::Ult,
                    };
                    self.push_node(InstrNode::new(Inst::ICmp {
                            op: hi_op,
                            ty: scrut_ty.clone(),
                            lhs: scrut_val,
                            rhs: hi_c,
                        })
                        .with_result(hi_cmp),
                    );
                    self.seal_with(Inst::CondBr {
                        cond: hi_cmp,
                        then_target: *body_blk,
                        then_args: vec![],
                        else_target: next_fallthrough,
                        else_args: vec![],
                    });

                    // The range arm's body block: bind `n @` (if any) to the scrutinee, then lower.
                    // The binding is a FRESH per-arm local, so the join merge ignores it.
                    self.locals = pre_locals.clone();
                    if let Some(var) = binding {
                        self.set_local(*var, scrut_val, scrut_ty.clone());
                    }
                    captured.push(self.lower_match_arm(
                        span,
                        value_producing,
                        *body_blk,
                        *body,
                        "Match(range arm no value)",
                    ));
                }
            }
        }

        // 6c. The terminal default arm.
        self.locals = pre_locals.clone();
        // Trust (wave-Q): an unguarded by-value binding default (`n => body`) binds the scrutinee to
        // `n` before the body — a FRESH per-arm local (never in `pre_locals`), so the join merge
        // ignores it, exactly like a guarded catch-all's / range arm's binding above. The scrutinee
        // value dominates the default block, so this is a local-map entry, no instruction. A plain
        // `_` default (`default_bind == None`) binds nothing.
        if let Some(var) = default_bind {
            self.set_local(var, scrut_val, scrut_ty.clone());
        }
        captured.push(self.lower_match_arm(
            span,
            value_producing,
            default_id,
            default_body,
            "Match(default arm no value)",
        ));

        // 7. Merge at the join — the same deferred-`Br` machinery as `lower_if` (steps 7-8 there).
        //    If no arm reaches the join it is unreachable: every captured arm already sealed
        //    (Diverged), so just restore the env and bail.
        let any_reaches_join = captured.iter().any(|a| a.is_reaching());
        if !any_reaches_join {
            self.locals = pre_locals;
            return None;
        }
        // Locals merged at the join: those whose value in a reaching arm differs from pre-split.
        let arm_refs: Vec<&CapturedArm> = captured.iter().collect();
        let merged: Vec<(LocalVarId, Ty)> = self.merged_locals(&pre_locals, &arm_refs);
        // The join's result value id (only when value-producing), then one param per merged local,
        // in a fixed order shared by every predecessor's `Br` args.
        let join_param = if value_producing { Some(self.fresh()) } else { None };
        let merged_params: Vec<(ValueId, Ty)> =
            merged.iter().map(|(_, ty)| (self.fresh(), ty.clone())).collect();
        // Seal each reaching arm's deferred `Br`, passing [result?] ++ [merged-local values].
        for arm in captured {
            self.seal_arm_into_join(arm, join_id, join_param.is_some(), &pre_locals, &merged);
        }
        // Open the join with [result?] ++ merged-local params; rebind each merged local to its new
        // join param so a use after the match sees the merged value.
        let mut join_params: Vec<(ValueId, Ty)> = Vec::new();
        if let Some(r) = join_param {
            join_params.push((r, result_ty));
        }
        join_params.extend(merged_params.iter().cloned());
        // Restore to the pre-split environment, then layer the merged-local rebinds on top.
        self.locals = pre_locals;
        self.start_block(join_id, join_params);
        for ((var, ty), (param, _)) in merged.iter().zip(merged_params.iter()) {
            self.set_local(*var, *param, ty.clone());
        }
        join_param
    }

    /// Lower one `match` arm body into block `blk` and CAPTURE it for the deferred-`Br` join merge
    /// (mirrors `lower_if`'s per-arm handling exactly): a diverged arm (or a value-producing arm
    /// with no value, sealed `Unreachable` + recorded via `label`) comes back `Diverged`; otherwise
    /// the open block + post-arm locals + result are snapshotted as `Reaching` and the caller seals
    /// its `Br` once the merged-local set is known.
    fn lower_match_arm(
        &mut self,
        span: rustc_span::Span,
        value_producing: bool,
        blk: BlockId,
        body: ExprId,
        label: &'static str,
    ) -> CapturedArm {
        self.start_block(blk, vec![]);
        let val = self.lower_expr(body);
        self.capture_arm(span, value_producing, val, label)
    }

    /// Trust: lower `match b { true => …, false => …, _ => … }` on a BOOL scrutinee. Built MIR
    /// gives a bool match the `if` encoding — `SwitchInt(b) -> [0: false-arm, otherwise: true-arm]`
    /// (`TerminatorKind::if_`'s `SwitchTargets::static_if(0, else, then)`) — so the faithful
    /// trust-ir shape is a `CondBr` + two arm blocks + the SAME deferred-`Br` block-param join
    /// `lower_if` uses (steps 2-8 there, mirrored exactly), NOT a `Switch` with Bool constants
    /// (the integer path's `Switch` compares in the integer Constant domain).
    ///
    /// Arm assignment is first-match-wins in source order: a `true`/`false` literal arm claims its
    /// value if unclaimed; a wildcard claims every still-unclaimed value. A single wildcard
    /// claiming BOTH values is straight-line (no branch — the scrutinee is still lowered for its
    /// effects, then the body inline, exactly a block expression).
    ///
    /// FAIL-CLOSED: a guarded arm, a binding/or/`@`/nested pattern, an arm that can never match
    /// (both values already claimed — the two-block `CondBr` has no place for its type-checked
    /// body), or a claim hole after classification (non-exhaustive — impossible past typeck,
    /// checked anyway) → recorded `unsupported`, no `CondBr` emitted.
    fn lower_bool_match(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
    ) -> Option<ValueId> {
        // 1. Classify WITHOUT mutating IR state (mirrors `lower_match` step 1; the closure only
        //    reads `self.thir`, so the borrow ends at `collect` before any `unsupported` push).
        enum ArmClass {
            Lit(bool, ExprId),
            Wild(ExprId),
            Reject(&'static str),
        }
        let classes: Vec<ArmClass> = arms
            .iter()
            .map(|arm_id| {
                let arm = &self.thir.arms[*arm_id];
                if arm.guard.is_some() {
                    return ArmClass::Reject("Match(guarded bool arm)");
                }
                match &arm.pattern.kind {
                    PatKind::Wild => ArmClass::Wild(arm.body),
                    PatKind::Constant { value } if value.ty.is_bool() => {
                        match value.try_to_bool() {
                            Some(b) => ArmClass::Lit(b, arm.body),
                            None => ArmClass::Reject("Match(bool pattern unreadable)"),
                        }
                    }
                    // A bare `n` catch-all stays scoped out exactly like the integer path's
                    // unguarded-binding arm; or/`@`/nested patterns are not lowered.
                    PatKind::Binding { .. } => ArmClass::Reject("Match(unguarded binding arm)"),
                    _ => ArmClass::Reject("Match(unsupported pattern)"),
                }
            })
            .collect();

        // 2. First-match-wins claim of the two values.
        let mut true_body: Option<ExprId> = None;
        let mut false_body: Option<ExprId> = None;
        for class in classes {
            match class {
                ArmClass::Reject(why) => {
                    self.unsupported.push((format!("{span:?}"), why));
                    return None;
                }
                ArmClass::Lit(b, body) => {
                    let slot = if b { &mut true_body } else { &mut false_body };
                    if slot.is_some() {
                        // The arm can never match — the two-block CondBr has no place for its
                        // (type-checked) body. Fail closed rather than drop it silently.
                        self.unsupported.push((format!("{span:?}"), "Match(unreachable arm)"));
                        return None;
                    }
                    *slot = Some(body);
                }
                ArmClass::Wild(body) => {
                    if true_body.is_some() && false_body.is_some() {
                        self.unsupported.push((format!("{span:?}"), "Match(unreachable arm)"));
                        return None;
                    }
                    true_body = true_body.or(Some(body));
                    false_body = false_body.or(Some(body));
                }
            }
        }
        // Typeck exhaustiveness guarantees both values are claimed; checked, not assumed.
        let (Some(then_body), Some(else_body)) = (true_body, false_body) else {
            self.unsupported.push((format!("{span:?}"), "Match(bool non-exhaustive)"));
            return None;
        };

        // 3. Scrutinee into the current (predecessor) block.
        let scrut_val = match self.lower_expr(scrutinee) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Match(scrutinee unsupported)"));
                return None;
            }
        };

        // 3a. A single wildcard claimed BOTH values (one body ExprId — distinct arms always carry
        //     distinct body ids): no dispatch at all. The scrutinee was evaluated for its effects;
        //     the body continues straight-line in the current block.
        if then_body == else_body {
            return self.lower_expr(then_body);
        }

        // 4-8. The `lower_if` join machinery, mirrored exactly (steps 2-8 there), with the
        //      already-lowered scrutinee as the branch condition.
        let result_ty = self.map_ty(result_rty);
        let value_producing = !matches!(result_ty, Ty::Unit);
        let then_id = self.fresh_block_id();
        let else_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();
        self.seal_with(Inst::CondBr {
            cond: scrut_val,
            then_target: then_id,
            then_args: vec![],
            else_target: else_id,
            else_args: vec![],
        });
        let pre_locals = self.locals.clone();
        self.start_block(then_id, vec![]);
        let then_val = self.lower_expr(then_body);
        let then_arm =
            self.capture_arm(span, value_producing, then_val, "Match(case arm no value)");
        self.locals = pre_locals.clone();
        self.start_block(else_id, vec![]);
        let else_val = self.lower_expr(else_body);
        let else_arm =
            self.capture_arm(span, value_producing, else_val, "Match(case arm no value)");
        if !then_arm.is_reaching() && !else_arm.is_reaching() {
            self.locals = pre_locals;
            return None;
        }
        let merged: Vec<(LocalVarId, Ty)> =
            self.merged_locals(&pre_locals, &[&then_arm, &else_arm]);
        let join_param = if value_producing { Some(self.fresh()) } else { None };
        let merged_params: Vec<(ValueId, Ty)> =
            merged.iter().map(|(_, ty)| (self.fresh(), ty.clone())).collect();
        self.seal_arm_into_join(then_arm, join_id, join_param.is_some(), &pre_locals, &merged);
        self.seal_arm_into_join(else_arm, join_id, join_param.is_some(), &pre_locals, &merged);
        let mut join_params: Vec<(ValueId, Ty)> = Vec::new();
        if let Some(r) = join_param {
            join_params.push((r, result_ty));
        }
        join_params.extend(merged_params.iter().cloned());
        self.locals = pre_locals;
        self.start_block(join_id, join_params);
        for ((var, ty), (param, _)) in merged.iter().zip(merged_params.iter()) {
            self.set_local(*var, *param, ty.clone());
        }
        join_param
    }

    /// Trust: lower a TUPLE/STRUCT-scrutinee `match`. Three shapes lower faithfully; every other
    /// shape pushes a precise `unsupported` tag and returns `None` (FAITHFUL-OR-FAIL-CLOSED).
    ///
    /// IRREFUTABLE single-arm destructure (`let (a, b) = t`, `let P { x, y } = p`,
    /// `match t { (a, b) => body }`): built MIR emits NO dispatch — the bindings are field
    /// projections of the scrutinee place and the body is straight-line — so the faithful
    /// trust-ir is: lower the scrutinee (an already-modeled aggregate), `ExtractField` each bound
    /// element (the `ExprKind::Field` projection + scalar gate), bind the pattern locals, lower
    /// the body INLINE. No blocks, no join; the pattern bindings are fresh `LocalVarId`s so
    /// leaving them bound past the arm cannot collide. Preserved byte-identical from wave-13.
    ///
    /// REFUTABLE multi-arm match over SCALAR tuple/struct fields with INTEGER/CHAR-literal element
    /// patterns (`match (x, y) { (0, b) => .., (1, _) => .., _ => .. }`): mirrors the enum/integer
    /// match control flow. Each earlier arm is a first-match-wins short-circuit CHAIN of per-field
    /// `ICmp{Eq}` tests — there is NO `BinOp::And` in the interpretable IR (`eval_binop`/`eval_icmp`
    /// expect ints), so per-field tests AND-combine via `CondBr` chaining exactly like the range
    /// path: a test miss branches to the SAME next-arm entry. EXACTLY the LAST arm must be
    /// irrefutable (the terminal catch-all) and no earlier arm may be, so the chain terminates at a
    /// matching body with no dead fell-through edge. Each tested-or-bound field is `ExtractField`'d
    /// ONCE in the predecessor (dominating all bodies); bodies merge through the SAME deferred-`Br`
    /// block-param join `lower_enum_match` uses.
    ///
    /// UNIT match `match () { () => body }`: lower the scrutinee (for effects), then body inline.
    ///
    /// FAIL-CLOSED (precise tags): a guarded arm; a bool/float/str/byte-string/aggregate literal
    /// field; an integer RANGE field; an or-pattern; a nested tuple/struct/variant/deref/box/slice
    /// subpattern; a by-ref/`@`/mut-ref binding; a non-scalar by-value field binding; a whole-value
    /// binding (the `for`-loop `mut iter` case); a non-terminal or absent terminal irrefutable arm
    /// (`non-exhaustive-refutable`); a borrow-pointer scrutinee; a scrutinee whose mapped type is
    /// neither `Ty::Tuple`, a registered `Ty::Struct`, nor `Ty::Unit`.
    ///
    /// Trust (wave-27): SYNTACTIC destructure plan for a single-arm irrefutable match whose
    /// scrutinee is itself a LITERAL tuple expression `(e0, .., eN)` (peeling Scope/Use) and whose
    /// arm is an unguarded `Leaf` of only `Wild` / by-value `ByRef::No` bindings that COVER every
    /// field. Returns `(element exprs, per-field Option<bound var>, body)`; `None` otherwise (caller
    /// falls through to the classifier). Pure read of `self.thir` — no IR mutation. Lowering each
    /// element expr DIRECTLY (never building the tuple value) is the exact per-element evaluation
    /// `let (a, b) = (u, v)` gives, and it is the ONLY path that admits a tuple of BORROW POINTERS:
    /// the `assert_eq!`/`assert_ne!` desugar is `match (&l, &r) { (lv, rv) => .. }`, and building
    /// the value tuple would trip the `Tuple(borrow ptr field)` escape guard, whereas a syntactic
    /// destructure lets `lv`/`rv` carry the elements' own registered borrow ptrs so `*lv == *rv` and
    /// the cold diverging `assert_failed` call all lower clean. Mirrors `lower_closure_call_untupled`.
    fn literal_tuple_destructure_plan(
        &self,
        scrutinee: ExprId,
        arm_id: ArmId,
    ) -> Option<(Vec<ExprId>, Vec<Option<LocalVarId>>, ExprId)> {
        let mut s = scrutinee;
        loop {
            match &self.thir.exprs[s].kind {
                ExprKind::Scope { value, .. } => s = *value,
                ExprKind::Use { source } => s = *source,
                _ => break,
            }
        }
        let ExprKind::Tuple { fields } = &self.thir.exprs[s].kind else {
            return None;
        };
        let field_exprs: Vec<ExprId> = fields.iter().copied().collect();
        let arm = &self.thir.arms[arm_id];
        if arm.guard.is_some() {
            return None;
        }
        let PatKind::Leaf { subpatterns } = &arm.pattern.kind else {
            return None;
        };
        let mut bind_map: Vec<Option<LocalVarId>> = vec![None; field_exprs.len()];
        let mut covered = vec![false; field_exprs.len()];
        for sp in subpatterns {
            let idx = sp.field.as_usize();
            if idx >= field_exprs.len() {
                return None;
            }
            covered[idx] = true;
            match &sp.pattern.kind {
                PatKind::Wild => {}
                PatKind::Binding {
                    var,
                    mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                    subpattern: None,
                    ..
                } => bind_map[idx] = Some(*var),
                // a literal test / nested / by-ref / `@` subpattern — not a straight destructure;
                // let the classifier handle (or reject) it.
                _ => return None,
            }
        }
        // Every field must be covered so every element is evaluated for effects (a `..` rest
        // pattern leaves some uncovered → bail to the classifier).
        if !covered.iter().all(|&c| c) {
            return None;
        }
        Some((field_exprs, bind_map, arm.body))
    }

    fn lower_tuple_match(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
    ) -> Option<ValueId> {
        // 0. The scrutinee's mapped type. A UNIT scrutinee (`match () { () => body }`) has no
        //    fields — an irrefutable match with no dispatch: lower the scrutinee (for effects),
        //    then the body inline. Owned data only (the `self.thir` borrow ends before mutation).
        let scrut_rty = self.thir.exprs[scrutinee].ty;
        let mapped = self.map_ty(scrut_rty);
        if matches!(mapped, Ty::Unit) {
            if arms.len() != 1 {
                self.unsupported.push((format!("{span:?}"), "TupleMatch(unit multi-arm)"));
                return None;
            }
            let (guarded, body) = {
                let arm = &self.thir.arms[arms[0]];
                (arm.guard.is_some(), arm.body)
            };
            if guarded {
                self.unsupported.push((format!("{span:?}"), "TupleMatch(guarded arm)"));
                return None;
            }
            let _ = self.lower_expr(scrutinee);
            return self.lower_expr(body);
        }

        // Trust (wave-27): SYNTACTIC destructure fast-path for a single-arm irrefutable match whose
        // scrutinee is a LITERAL tuple expr `(e0, .., eN)`. Bind each pattern field directly to
        // `lower_expr(e_idx)` — NEVER materializing the tuple value — so a tuple of BORROW POINTERS
        // (`assert_eq!`/`assert_ne!` desugar `match (&l, &r) { (lv, rv) => .. }`) does not trip the
        // `Tuple(borrow ptr field)` escape guard, and each bound var carries the element's own
        // registered borrow ptr (so `*lv == *rv` + the cold diverging `assert_failed` call all lower
        // clean). GATED to fire ONLY when >=1 BOUND field is non-scalar — exactly the case the
        // `ExtractField` classifier below REJECTS at `is_scalar_ty` (`TupleMatch(non-scalar field
        // binding)`), so every currently-clean all-scalar tuple match keeps its byte-identical
        // `ExtractField` lowering (became_dirty == 0). Semantically exact: a full destructure of a
        // literal tuple IS elementwise binding in source order; the tuple temp is dead after, so its
        // identity never matters. Every other shape (multi-arm, guarded, refutable, non-literal
        // scrutinee, nested/by-ref subpattern, `..` rest) falls through to the classifier unchanged.
        if arms.len() == 1 {
            if let Some((field_exprs, bind_map, body)) =
                self.literal_tuple_destructure_plan(scrutinee, arms[0])
            {
                let any_nonscalar_bound = (0..field_exprs.len()).any(|i| {
                    // EXACT complement of the classifier's per-field accept test
                    // (`is_scalar_ty(map_ty(field_ty))` at the `ExtractField` path below): fire the
                    // fast-path iff some BOUND field's MAPPED type is non-scalar. Gate on the MAPPED
                    // type, NOT a raw `ty.kind()` check — `map_ty` peels `ty::Pat`→base scalar
                    // (lib.rs:921) and normalizes a scalar `ty::Alias`, so a raw-kind check would
                    // wrongly divert a currently-CLEAN pattern-typed / scalar-alias-typed match onto
                    // this path (a `became_dirty` regression: same source, structurally different
                    // trust-ir). A scalar-resolving type records no gap, and any type that WOULD
                    // record a gap is non-scalar and fires the gate regardless — so reusing `map_ty`
                    // here is side-effect-safe. Keeps every currently-clean tuple match on its
                    // byte-identical `ExtractField` lowering (became_dirty == 0 by construction).
                    bind_map[i].is_some()
                        && !is_scalar_ty(&self.map_ty(self.thir.exprs[field_exprs[i]].ty))
                });
                if any_nonscalar_bound {
                    for i in 0..field_exprs.len() {
                        let fexpr = field_exprs[i];
                        let fty = self.map_ty(self.thir.exprs[fexpr].ty);
                        match self.lower_expr(fexpr) {
                            Some(v) => {
                                if let Some(var) = bind_map[i] {
                                    self.set_local(var, v, fty);
                                }
                            }
                            None => {
                                // An element failed to lower (records its own gap). Fail closed.
                                self.unsupported.push((
                                    format!("{span:?}"),
                                    "TupleMatch(literal-tuple element unsupported)",
                                ));
                                return None;
                            }
                        }
                    }
                    return self.lower_expr(body);
                }
            }
        }

        // 1. The scrutinee's mapped element types (`map_ty` records its own gaps; an empty tuple
        //    mapped to `Ty::Unit` was handled above). A STRUCT scrutinee (`let P { x, y } = p` —
        //    the same `PatKind::Leaf` shape) maps to `Ty::Struct(id)`; its element types are the
        //    registered def's fields in declaration order — the exact indices `sp.field` carries.
        let elem_tys = match &mapped {
            Ty::Tuple(elem_tys) => elem_tys.clone(),
            Ty::Struct(sid) => match self.registered_struct_field_tys(*sid) {
                Some(f) => f,
                None => {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(unregistered struct id)"));
                    return None;
                }
            },
            _ => {
                self.unsupported.push((format!("{span:?}"), "TupleMatch(non-tuple mapped ty)"));
                return None;
            }
        };

        // 2. Classify every arm WITHOUT mutating IR state (the `self.thir` borrow ends at `collect`,
        //    before any `unsupported` push). An arm is IRREFUTABLE (a `_`, or a `Leaf` of only
        //    `Wild`/by-value-scalar bindings — no tests), REFUTABLE (a `Leaf` with >=1 integer/char
        //    literal field test), or a precise `Reject`. `tcx` is `Copy` and `elem_tys` owned — both
        //    usable in the read-only closure. Per-field signedness/width are read from the mapped
        //    field type (`Ty::Char` supplies a 32-bit unsigned carrier), matching the
        //    integer-`Switch` `const_pat_int` domain.
        enum ArmClass {
            // bindings [(field, local)], body.
            Irrefutable(Vec<(u32, LocalVarId)>, ExprId),
            // tests [(field, literal)], bindings [(field, local)], body.
            Refutable(Vec<(u32, u128)>, Vec<(u32, LocalVarId)>, ExprId),
            Reject(&'static str),
        }
        let tcx = self.tcx;
        let classes: Vec<ArmClass> = arms
            .iter()
            .map(|arm_id| {
                let arm = &self.thir.arms[*arm_id];
                if arm.guard.is_some() {
                    return ArmClass::Reject("TupleMatch(guarded arm)");
                }
                // Normalize the arm pattern into a POSITIONAL `(index, subpattern)` list, shared by
                // the tuple/struct (`PatKind::Leaf`, index = declared field) and, Trust (wave-AM),
                // the FIXED-LENGTH ARRAY (`PatKind::Array`, index = element position) forms. map_ty
                // already lowered `[T; N]` (N>0) to `Ty::Tuple([T; N])` (lib.rs ~959), so the
                // downstream `ExtractField idx` element read is IDENTICAL for both — a const array
                // index is `ExtractField` too (the `ExprKind::Index` fast-path). A REST pattern
                // (`[a, .., c]` → `slice: Some`) binds a subslice (a distinct fat-slice shape) and is
                // OUT OF SCOPE (fail-closed); a `PatKind::Slice` scrutinee (`&[T]`) is not `ty::Array`
                // and never routes here.
                let positional: Vec<(u32, &Pat<'tcx>)> = match &arm.pattern.kind {
                    PatKind::Wild => return ArmClass::Irrefutable(Vec::new(), arm.body),
                    PatKind::Leaf { subpatterns } => {
                        subpatterns.iter().map(|sp| (sp.field.as_u32(), &sp.pattern)).collect()
                    }
                    PatKind::Array { prefix, slice: None, suffix } => {
                        // No `..` rest: `prefix` is the full element list in order (`suffix` is empty,
                        // but chain it defensively). Positional index = element position.
                        prefix
                            .iter()
                            .chain(suffix.iter())
                            .enumerate()
                            .map(|(i, p)| (i as u32, p))
                            .collect()
                    }
                    // Trust (wave-SR): a `..` REST that BINDS NOTHING (`[a, b, ..]`, `[.., a, b]`,
                    // `[a, .., b]`, `[..]`) is a pure fixed-position classifier — the IGNORED middle
                    // needs no subslice value. Prefix elems keep index `0..prefix.len()`; suffix elems
                    // get the TAIL index `n - suffix.len() + j` (n = array length = the mapped tuple
                    // arity `elem_tys.len()`). A `rest @ ..` subslice BINDING (build_bind_node proves it
                    // binds — the wave-NS certificate) stays fail-closed: a distinct fat-slice shape
                    // wave-SR does not model. `became_dirty == 0` by construction — every rest pattern
                    // Rejected before this wave, so no clean body traversed this arm.
                    PatKind::Array { prefix, slice: Some(rest), suffix } => {
                        let binds_rest = match build_bind_node(rest) {
                            Some(node) => bind_node_binds(&node),
                            None => true, // cannot prove it binds nothing → fail closed
                        };
                        if binds_rest {
                            return ArmClass::Reject("TupleMatch(array rest binding)");
                        }
                        let n = elem_tys.len();
                        let ns = suffix.len();
                        if prefix.len() + ns > n {
                            return ArmClass::Reject("TupleMatch(array rest arity)");
                        }
                        prefix
                            .iter()
                            .enumerate()
                            .map(|(i, p)| (i as u32, p))
                            .chain(suffix.iter().enumerate().map(|(j, p)| ((n - ns + j) as u32, p)))
                            .collect()
                    }
                    PatKind::Slice { .. } => {
                        // A `&[T]`/`[T]` SLICE scrutinee (not a fixed `ty::Array`) — a distinct fat-slice
                        // shape that never routes to this array/tuple classifier; fail closed.
                        return ArmClass::Reject("TupleMatch(slice scrutinee)");
                    }
                    PatKind::Or { .. } => return ArmClass::Reject("TupleMatch(or-pattern)"),
                    // whole-value binding / deref / … — not modeled (keeps the `for`-loop
                    // `mut iter` whole-value binding fail-closed).
                    _ => return ArmClass::Reject("TupleMatch(unsupported pattern)"),
                };
                let mut tests: Vec<(u32, u128)> = Vec::new();
                let mut binds: Vec<(u32, LocalVarId)> = Vec::new();
                for (idx, subpat) in positional {
                    let Some(field_ty) = elem_tys.get(idx as usize) else {
                        return ArmClass::Reject("TupleMatch(field out of range)");
                    };
                    match &subpat.kind {
                        PatKind::Wild => {}
                        PatKind::Binding {
                            var,
                            mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                            subpattern: None,
                            ..
                        } => {
                            if !is_scalar_ty(field_ty) {
                                return ArmClass::Reject("TupleMatch(non-scalar field binding)");
                            }
                            binds.push((idx, *var));
                        }
                        // by-ref / `@` / mut-ref binding — not modeled.
                        PatKind::Binding { .. } => {
                            return ArmClass::Reject("TupleMatch(by-ref subpattern)");
                        }
                        PatKind::Constant { value } => {
                            let signed =
                                matches!(field_ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128);
                            let bits = scrut_ty_bits(field_ty);
                            match const_pat_int(tcx, *value, signed, bits) {
                                Some(lit) => tests.push((idx, lit)),
                                // `const_pat_int` declines bool/float/str/aggregate; tag by the
                                // const's type so the residue census stays honest.
                                None => {
                                    return ArmClass::Reject(match value.ty.kind() {
                                        ty::Bool => "TupleMatch(bool literal field)",
                                        ty::Float(_) => "TupleMatch(float literal field)",
                                        _ => "TupleMatch(non-scalar literal field)",
                                    });
                                }
                            }
                        }
                        PatKind::Range(_) => return ArmClass::Reject("TupleMatch(range field)"),
                        // Trust (B3-2a/B3-2c): a NILADIC variant pattern on an enum tuple field
                        // (`(E::A, x)`, `(None, y)`) is a discriminant TEST. The tested field's
                        // Switch key is field 0 of the first-class `Ty::Enum`, using its
                        // registered canonical tag representation;
                        // `tests` carries the variant's `discriminant_for_variant`, and the
                        // extraction (step 5) reads that tag or fails closed.
                        // Payload-bearing variant patterns (`(Some(z), _)`) stay fail-closed — a
                        // payload binding needs the enum model's payload slot, out of scope here.
                        // `adt_def` + `tcx` (both `Copy`, captured) suffice; no `&self` borrow.
                        PatKind::Variant { adt_def, variant_index, subpatterns, .. } => {
                            if !subpatterns.is_empty() {
                                return ArmClass::Reject("TupleMatch(variant payload subpattern)");
                            }
                            let discr = adt_def.discriminant_for_variant(tcx, *variant_index).val;
                            if i64::try_from(discr as i128).is_err() {
                                return ArmClass::Reject(
                                    "TupleMatch(variant discriminant exceeds i64)",
                                );
                            }
                            tests.push((idx, discr));
                        }
                        PatKind::Or { .. } => return ArmClass::Reject("TupleMatch(or-pattern)"),
                        // Trust (wave-NS): a nested subpattern that is IRREFUTABLE and binds NOTHING —
                        // a fieldless unit-struct pattern `S` (`PatKind::Leaf { subpatterns: [] }`, e.g.
                        // `match x { (S, ..) => .. }` on `x: (S, Z, W)`), or an all-`_` nested tuple/
                        // array (`((_, _), _)`). `build_bind_node` returning `Some` is the irrefutable-
                        // by-value certificate (it declines `ref`/const/range/variant/or/deref/box/
                        // slice/array-rest → `None`, and `PatKind::Constant`/`Range`/`Variant`/`Or`/
                        // `Binding` are matched earlier), and `!bind_node_binds` means the nested pattern
                        // binds no local — so it is a pure NO-OP field: no test, no bind, no
                        // `ExtractField` emitted. IR is byte-identical to the same arm with this field
                        // replaced by `_`, so `became_dirty == 0` by construction (this `_` arm ALWAYS
                        // returned `Reject` before, so no currently-clean body traversed it). A nested
                        // subpattern that WOULD bind a local (`((a, b), _)`) stays fail-closed: the flat
                        // `binds: Vec<(u32, LocalVarId)>` carrier cannot represent a nested binding, and
                        // that full `BindNode` carrier through the multi-arm join is deliberately out of
                        // scope (zero corpus bodies).
                        _ => match build_bind_node(subpat) {
                            Some(node) if !bind_node_binds(&node) => {}
                            _ => return ArmClass::Reject("TupleMatch(nested subpattern)"),
                        },
                    }
                }
                if tests.is_empty() {
                    ArmClass::Irrefutable(binds, arm.body)
                } else {
                    ArmClass::Refutable(tests, binds, arm.body)
                }
            })
            .collect();

        // Surface the FIRST reject (mirrors the enum/integer path's reject-on-first semantics).
        for c in &classes {
            if let ArmClass::Reject(why) = c {
                self.unsupported.push((format!("{span:?}"), *why));
                return None;
            }
        }
        let n = classes.len();
        if n == 0 {
            self.unsupported.push((format!("{span:?}"), "TupleMatch(no arms)"));
            return None;
        }

        // 3. SINGLE-ARM fast path (wave-13 `let (a, b) = t`): one irrefutable arm → straight-line
        //    destructure, no blocks, no join — IDENTICAL to the pre-wave-18 lowering.
        if n == 1 {
            let (binds, body) = match classes.into_iter().next().unwrap() {
                ArmClass::Irrefutable(binds, body) => (binds, body),
                // A lone refutable arm is a non-exhaustive match (no catch-all); fail closed.
                ArmClass::Refutable(..) => {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(non-exhaustive-refutable)"));
                    return None;
                }
                ArmClass::Reject(why) => {
                    self.unsupported.push((format!("{span:?}"), why));
                    return None;
                }
            };
            let scrut_val = match self.lower_expr(scrutinee) {
                Some(v) => v,
                None => {
                    self.unsupported.push((format!("{span:?}"), "Match(scrutinee unsupported)"));
                    return None;
                }
            };
            if self.is_borrow_ptr(scrut_val) {
                // `match *r { … }` on a deref'd tuple — the scrutinee is a pointer, not the
                // aggregate value. Fail closed.
                self.unsupported.push((format!("{span:?}"), "TupleMatch(scrutinee is borrow ptr)"));
                return None;
            }
            for (idx, var) in binds {
                let Some(ety) = elem_tys.get(idx as usize).cloned() else {
                    self.unsupported.push((format!("{span:?}"), "TupleMatch(field out of range)"));
                    return None;
                };
                if !is_scalar_ty(&ety) {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(non-scalar field binding)"));
                    return None;
                }
                let v = self.fresh();
                self.push_node(InstrNode::new(Inst::ExtractField {
                        ty: ety.clone(),
                        aggregate: scrut_val,
                        field: idx,
                    })
                    .with_result(v),
                );
                self.set_local(var, v, ety);
            }
            return self.lower_expr(body);
        }

        // 4. MULTI-ARM refutable path. Structural requirement (CHECKED, not assumed): EXACTLY the
        //    last arm is irrefutable (the terminal catch-all) and NO earlier arm is (an earlier
        //    catch-all makes successors unreachable). Well-typed integer-field matches always
        //    satisfy this; anything else fails closed as `non-exhaustive-refutable`.
        let mut ref_arms: Vec<(Vec<(u32, u128)>, Vec<(u32, LocalVarId)>, ExprId)> = Vec::new();
        let mut terminal: Option<(Vec<(u32, LocalVarId)>, ExprId)> = None;
        for (i, c) in classes.into_iter().enumerate() {
            let is_last = i == n - 1;
            match c {
                ArmClass::Irrefutable(binds, body) => {
                    if !is_last {
                        self.unsupported
                            .push((format!("{span:?}"), "TupleMatch(non-exhaustive-refutable)"));
                        return None;
                    }
                    terminal = Some((binds, body));
                }
                ArmClass::Refutable(tests, binds, body) => {
                    if is_last {
                        // Trust (wave-A4): an EXHAUSTIVE match with no explicit `_` (a fieldless-
                        // enum / bool tuple match: `(E::A,x)=>.., (E::B,y)=>..`) has a REFUTABLE
                        // last arm. rustc GUARANTEES exhaustiveness before we lower (a non-`_`
                        // integer match cannot typecheck), so once every earlier arm misses, the
                        // last arm's case is the ONLY residual: drop its tests and make it the
                        // default terminal — exactly `lower_enum_match`'s pop-last-as-default.
                        // Reached only when `terminal` is still None (an explicit `_`/Wild already
                        // set it via the Irrefutable branch, which is `is_last`-gated too), and it
                        // only ADDS candidates (a refutable last arm was `non-exhaustive-refutable`
                        // fail-closed before), so became_dirty == 0 by construction. Guards are
                        // rejected at classify, so no guard-false route is needed for the default.
                        terminal = Some((binds, body));
                    } else {
                        ref_arms.push((tests, binds, body));
                    }
                }
                ArmClass::Reject(why) => {
                    self.unsupported.push((format!("{span:?}"), why));
                    return None;
                }
            }
        }
        let (terminal_binds, terminal_body) = match terminal {
            Some(t) => t,
            None => {
                self.unsupported
                    .push((format!("{span:?}"), "TupleMatch(non-exhaustive-refutable)"));
                return None;
            }
        };

        // 5. Lower the scrutinee ONCE, then `ExtractField` the UNION of every tested-or-bound field
        //    ONCE in the predecessor — each dominates all test/body blocks. Every extracted field is
        //    scalar (tested fields passed `const_pat_int`; bound fields passed `is_scalar_ty` at
        //    classify) EXCEPT a wave-A4 enum-variant-tested field, whose extracted value is its TAG
        //    (field 0, I64) — still a scalar Switch key; the gate here is defensive.
        let scrut_val = match self.lower_expr(scrutinee) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "Match(scrutinee unsupported)"));
                return None;
            }
        };
        if self.is_borrow_ptr(scrut_val) {
            self.unsupported.push((format!("{span:?}"), "TupleMatch(scrutinee is borrow ptr)"));
            return None;
        }
        let mut needed: Vec<u32> = Vec::new();
        for (tests, binds, _) in &ref_arms {
            for (idx, _) in tests {
                if !needed.contains(idx) {
                    needed.push(*idx);
                }
            }
            for (idx, _) in binds {
                if !needed.contains(idx) {
                    needed.push(*idx);
                }
            }
        }
        for (idx, _) in &terminal_binds {
            if !needed.contains(idx) {
                needed.push(*idx);
            }
        }
        needed.sort_unstable();
        let mut extracted: Vec<(u32, ValueId, Ty)> = Vec::new();
        for idx in needed {
            let Some(field_ty) = elem_tys.get(idx as usize).cloned() else {
                self.unsupported.push((format!("{span:?}"), "TupleMatch(field out of range)"));
                return None;
            };
            // Trust (B3-2a/B3-2c): a tested enum field carries its Switch key in
            // field 0 of the first-class `Ty::Enum` value. Enum-ness is keyed on
            // the Rust field type (`scrut_rty`); `field_ty` supplies the registered
            // enum id and canonical unsigned tag representation. Signed or absent
            // tag representations fail closed below.
            let field_rty: Option<RustcTy<'tcx>> = match scrut_rty.kind() {
                ty::Tuple(elems) => elems.get(idx as usize).copied(),
                ty::Array(elem, _) => Some(*elem),
                ty::Adt(adt, gargs) if adt.is_struct() => adt
                    .non_enum_variant()
                    .fields
                    .get(rustc_abi::FieldIdx::from_u32(idx))
                    .map(|f| f.ty(self.tcx, *gargs).skip_normalization()),
                _ => None,
            };
            if let Some(ty::Adt(adt, _gargs)) = field_rty.map(|t| t.kind()) {
                if adt.is_enum() {
                    // Trust (B3-2a G3): key the tag channel on the MAPPED field
                    // type — a first-class enum field maps
                    // first-class Ty::Enum whose tag lane is typed at the CANONICAL
                    // repr (may be U8/I32, never blindly I64; expect_ty is exact).
                    // Scope: UNSIGNED canonical reprs only (the raw
                    // discriminant_for_variant test values in `tests` are width-
                    // truncated patterns; a signed repr's sign-extension seam is out
                    // of this lane's scope — fail closed, same tag as before).
                    match &field_ty {
                        // Trust (B3-2c T2 slice 2): the wave-A4 legacy-Tuple tag
                        // lane is DELETED — no enum field maps Ty::Tuple([I64, ..])
                        // anymore; a first-class field takes the Ty::Enum arm below,
                        // everything else fails closed.
                        Ty::Enum(eid) => {
                            let tag_ty = self
                                .registered_enum(*eid)
                                .and_then(|d| d.canonical_tag_repr())
                                .map(|r| r.ty());
                            let Some(tag_ty @ (Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64)) = tag_ty
                            else {
                                self.unsupported.push((
                                    format!("{span:?}"),
                                    "TupleMatch(enum field not legacy-repr)",
                                ));
                                return None;
                            };
                            let agg = self.fresh();
                            self.push_node(InstrNode::new(Inst::ExtractField {
                                    ty: field_ty.clone(),
                                    aggregate: scrut_val,
                                    field: idx,
                                })
                                .with_result(agg),
                            );
                            let tag = self.fresh();
                            self.push_node(InstrNode::new(Inst::ExtractField {
                                    ty: tag_ty.clone(),
                                    aggregate: agg,
                                    field: 0,
                                })
                                .with_result(tag),
                            );
                            extracted.push((idx, tag, tag_ty));
                            continue;
                        }
                        _ => {
                            self.unsupported.push((
                                format!("{span:?}"),
                                "TupleMatch(enum field not legacy-repr)",
                            ));
                            return None;
                        }
                    }
                }
            }
            if !is_scalar_ty(&field_ty) {
                self.unsupported.push((format!("{span:?}"), "TupleMatch(non-scalar field)"));
                return None;
            }
            let v = self.fresh();
            self.push_node(InstrNode::new(Inst::ExtractField {
                    ty: field_ty.clone(),
                    aggregate: scrut_val,
                    field: idx,
                })
                .with_result(v),
            );
            extracted.push((idx, v, field_ty));
        }
        // Resolve a field index to its (once-extracted) SSA value + type. `needed` is the exact
        // union of referenced fields, so this never misses; a defensive `None` fails closed.
        let field_of = |idx: u32| -> Option<(ValueId, Ty)> {
            extracted.iter().find(|e| e.0 == idx).map(|e| (e.1, e.2.clone()))
        };

        // 6. Join shape (mirrors `lower_enum_match`): unit result → zero-param join.
        let result_ty = self.map_ty(result_rty);
        let value_producing = !matches!(result_ty, Ty::Unit);

        // 7. Allocate blocks: per refutable arm, one test block per field test + one body block;
        //    then the terminal arm's body block (also the last miss edge's target) and the join.
        let ref_blocks: Vec<(Vec<BlockId>, BlockId)> = ref_arms
            .iter()
            .map(|(tests, _, _)| {
                let tbs: Vec<BlockId> = (0..tests.len()).map(|_| self.fresh_block_id()).collect();
                (tbs, self.fresh_block_id())
            })
            .collect();
        let terminal_body_block = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // The entry a miss in refutable arm `i` branches to: the NEXT refutable arm's first test
        // block, or (for the last refutable arm) the terminal arm's body block. First-match-wins.
        let next_entry = |i: usize| -> BlockId {
            if i + 1 < ref_blocks.len() { ref_blocks[i + 1].0[0] } else { terminal_body_block }
        };

        // 8. Seal the predecessor into arm 0's first test block (every refutable arm has >=1 test).
        let pre_locals = self.locals.clone();
        self.seal_with(Inst::Br { target: ref_blocks[0].0[0], args: vec![] });

        // 9. Emit each refutable arm's short-circuit test chain: `f == c` per tested field, ANDed
        //    via `CondBr` chaining (true → next test / body; ANY false → the shared miss edge).
        for (i, (tests, _binds, _body)) in ref_arms.iter().enumerate() {
            let (tbs, body_block) = &ref_blocks[i];
            let miss = next_entry(i);
            for (j, (field_idx, lit)) in tests.iter().enumerate() {
                self.locals = pre_locals.clone();
                self.start_block(tbs[j], vec![]);
                let Some((field_val, field_ty)) = field_of(*field_idx) else {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(internal: unextracted field)"));
                    return None;
                };
                let c = self.fresh();
                let Some((bits, signed)) = int_scalar_bits(&field_ty) else {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(non-integer tested field)"));
                    return None;
                };
                self.push_node(InstrNode::new(Inst::Const {
                        ty: field_ty.clone(),
                        value: integer_constant_from_bits(*lit, signed, bits),
                    })
                    .with_result(c),
                );
                let ok = self.fresh();
                self.push_node(InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: field_ty,
                        lhs: field_val,
                        rhs: c,
                    })
                    .with_result(ok),
                );
                let then_target = if j + 1 < tbs.len() { tbs[j + 1] } else { *body_block };
                self.seal_with(Inst::CondBr {
                    cond: ok,
                    then_target,
                    then_args: vec![],
                    else_target: miss,
                    else_args: vec![],
                });
            }
        }

        // 10. Lower each arm's body (refutable bodies then the terminal body) with the SAME
        //     deferred-`Br` join merge as `lower_enum_match`: reset the env, bind each field local
        //     to its extracted value (a FRESH per-arm local, invisible to the merge), lower, capture.
        let mut captured: Vec<CapturedArm> = Vec::new();
        for (i, (_tests, binds, body)) in ref_arms.iter().enumerate() {
            let (_tbs, body_block) = &ref_blocks[i];
            self.locals = pre_locals.clone();
            self.start_block(*body_block, vec![]);
            for (field_idx, var) in binds {
                let Some((field_val, field_ty)) = field_of(*field_idx) else {
                    self.unsupported
                        .push((format!("{span:?}"), "TupleMatch(internal: unextracted field)"));
                    return None;
                };
                self.set_local(*var, field_val, field_ty);
            }
            let val = self.lower_expr(*body);
            captured.push(self.capture_arm(span, value_producing, val, "TupleMatch(arm no value)"));
        }
        self.locals = pre_locals.clone();
        self.start_block(terminal_body_block, vec![]);
        for (field_idx, var) in &terminal_binds {
            let Some((field_val, field_ty)) = field_of(*field_idx) else {
                self.unsupported
                    .push((format!("{span:?}"), "TupleMatch(internal: unextracted field)"));
                return None;
            };
            self.set_local(*var, field_val, field_ty);
        }
        let tval = self.lower_expr(terminal_body);
        captured.push(self.capture_arm(
            span,
            value_producing,
            tval,
            "TupleMatch(terminal arm no value)",
        ));

        // 11. Merge at the join (mirrors `lower_enum_match` step 8 exactly). If no arm reaches the
        //     join, it is unreachable: every captured arm already sealed, so restore env and bail.
        let any_reaches_join = captured.iter().any(|a| a.is_reaching());
        if !any_reaches_join {
            self.locals = pre_locals;
            return None;
        }
        let arm_refs: Vec<&CapturedArm> = captured.iter().collect();
        let merged: Vec<(LocalVarId, Ty)> = self.merged_locals(&pre_locals, &arm_refs);
        let join_param = if value_producing { Some(self.fresh()) } else { None };
        let merged_params: Vec<(ValueId, Ty)> =
            merged.iter().map(|(_, ty)| (self.fresh(), ty.clone())).collect();
        for arm in captured {
            self.seal_arm_into_join(arm, join_id, join_param.is_some(), &pre_locals, &merged);
        }
        let mut join_params: Vec<(ValueId, Ty)> = Vec::new();
        if let Some(r) = join_param {
            join_params.push((r, result_ty));
        }
        join_params.extend(merged_params.iter().cloned());
        self.locals = pre_locals;
        self.start_block(join_id, join_params);
        for ((var, ty), (param, _)) in merged.iter().zip(merged_params.iter()) {
            self.set_local(*var, *param, ty.clone());
        }
        join_param
    }

    /// Trust (B3-2c T2): enum match is GENERAL-ONLY — the legacy (I64, payload)
    /// tuple match body (~600 lines: classifier, guard chains, payload
    /// re-materialization) is DELETED. `lower_enum_match_general` carries the
    /// full surviving capability: the wave-MR2 ref-scrutinee peel, G1 guards,
    /// by-ref payload GEPs (L4G), niladic OR, and the 2c unit-field no-ops; it
    /// fails closed on unregistered enums (the opaque floor).
    fn lower_enum_match(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
    ) -> Option<ValueId> {
        self.lower_enum_match_general(result_rty, span, scrutinee, arms)
    }

    /// Lower one ENUM `match` arm into block `blk`: bind the payload subpattern (if any) to the
    /// scrutinee's already-extracted payload value, lower the body, and CAPTURE the arm for the
    /// deferred-`Br` join merge (mirrors `lower_match_arm`). The payload binding is a FRESH per-arm
    /// local, so it does not participate in the cross-join merge.
    #[allow(clippy::too_many_arguments)]
    /// Trust: lower a `match` over a first-class `Ty::Enum` scrutinee.
    ///
    ///   * the tag extract is typed with the `EnumDef`'s CANONICAL tag repr (`ExtractField
    ///     { ty: <canonical tag ty>, field: 0 }`) — the pinned interpreter types the tag lane
    ///     exactly so, and an `I64`-typed extract over a `U8` tag lane is a `TypeError`
    ///     (scratch-verified fail-closed, cmtest w5_enum (8c));
    ///   * payload bindings are `ExtractField`'d INSIDE each arm's block (not the predecessor):
    ///     the in-register aggregate is shaped `[tag, <selected variant's fields>]`, so a slot
    ///     only exists — with a variant-specific type — once the `Switch` has committed to that
    ///     variant's discriminant. Slot `1 + field_index`, per-variant field types, all read
    ///     from the REGISTERED `EnumDef` (the same source `lower_enum_construct_general` and
    ///     the `Switch` cases use — agreement by construction, cmtest w5_enum (3)/(4)).
    ///
    /// `Switch` cases carry the variants' EXPLICIT discriminant VALUES (negative explicit
    /// discriminants included — cmtest w5_enum (6)). Default selection uses
    /// a `_` arm, else the LAST variant arm of an exhaustive match.
    ///
    /// FAIL-CLOSED: a guarded arm, a by-ref/`@`/nested/or subpattern, a payload field index out
    /// of the variant's range, a scrutinee whose mapped type is not a registered `Ty::Enum`, a
    /// borrow-pointer scrutinee, or an unregistered variant/discriminant desync.
    fn lower_enum_match_general(
        &mut self,
        result_rty: RustcTy<'tcx>,
        span: rustc_span::Span,
        scrutinee: ExprId,
        arms: &[ArmId],
    ) -> Option<ValueId> {
        let scrut_rty = self.thir.exprs[scrutinee].ty;
        // Trust (wave-MR2): peel a SHARED ref-to-enum scrutinee (`r: &E`).
        // `deref_scrut` drives the discriminant read below (a deref-Load of the pointee Ty::Enum
        // value). By-value keeps `deref_scrut=false` (original path unchanged).
        let (map_from, deref_scrut) = match scrut_rty.kind() {
            ty::Ref(_, pointee, m) if m.is_not() => (*pointee, true),
            _ => (scrut_rty, false),
        };
        // The mapped scrutinee type registers (or re-finds) the EnumDef; bail if it degraded
        // (register_enum recorded its own tag then).
        let mapped = self.map_ty(map_from);
        let Ty::Enum(eid) = &mapped else {
            self.unsupported.push((format!("{span:?}"), "EnumMatch(non-enum mapped ty)"));
            return None;
        };
        let eid = *eid;
        // Snapshot the per-variant field types, discriminants, and canonical tag type out of
        // the registered def (clones: the `&mut self` calls below would hold the borrow).
        let (variant_field_tys, discriminants, tag_ty) = match self.registered_enum(eid) {
            Some(ed) => {
                let Some(tag) = ed.canonical_tag_repr() else {
                    // register_enum gates on this; missing here is a desync, not a shape.
                    self.unsupported.push((format!("{span:?}"), "EnumMatch(no canonical tag)"));
                    return None;
                };
                let fields: Vec<Vec<Ty>> = ed.variants.iter().map(|v| v.fields.clone()).collect();
                let discs: Vec<Option<i128>> = (0..ed.variants.len())
                    .map(|i| ed.discriminants.get(i).copied().flatten())
                    .collect();
                (fields, discs, tag.ty())
            }
            None => {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(unregistered enum id)"));
                return None;
            }
        };

        // 1. Classify each arm WITHOUT mutating IR state (mirrors `lower_enum_match` step 1).
        //    A `Variant` arm carries its variant index + its payload bindings
        //    (local, payload field index, `Option<byte-offset>` — `None` = by-VALUE `ExtractField`
        //    of the loaded aggregate; `Some(off)` = by-REF interior GEP of the scrutinee ptr at the
        //    field's rustc byte-offset, the general-model twin of wave-L4's legacy ref-payload bind).
        //    A `Wild` arm is the catch-all default.
        enum ArmClass {
            // Trust (B3-2b G1): the trailing `Option<ExprId>` is the arm GUARD (`V(x) if g`);
            // `None` for an unguarded arm (byte-identical to the pre-G1 lowering).
            Variant(usize, Vec<(LocalVarId, u32, Option<u64>)>, Option<ExprId>, ExprId),
            // Trust (wave-OR2): a niladic OR-pattern arm `E::A | E::B => body` on a first-class
            // `Ty::Enum` (payload enum matched WITHOUT binding) — variant INDICES routing to one
            // shared body. The general twin of the legacy `VariantOr`; expanded (WITH a dedup, as
            // the general case-build below does NOT dedup) to one `Variant(v, vec![], body)` per
            // index in the collection loop.
            VariantOr(Vec<usize>, ExprId),
            Wild(ExprId),
            Reject(&'static str),
        }
        // Copy `tcx` out so the by-ref offset's `layout_of` needs no `&self` borrow in the closure.
        let tcx = self.tcx;
        let classes: Vec<ArmClass> = arms
            .iter()
            .map(|arm_id| {
                let arm = &self.thir.arms[*arm_id];
                // Trust (B3-2b G1): a guarded VARIANT arm is now supported (guard-test block
                // + guard-false fallthrough, ported from the legacy path). A guarded WILDCARD
                // or OR arm stays rejected below — a guarded catch-all's guard-false route
                // must chain to the NEXT arm, which the wildcard-as-default shape cannot model.
                let arm_guard = arm.guard;
                // Trust (wave-MR2): DEREF-MATCH arm normalization — strip the single `&`-layer each
                // non-wild arm of a ref-to-enum match carries (mirrors wave-MR / the int deref-match).
                // A top-level binding binds the REFERENCE (ill-typed vs the LOADED pointee) → fail
                // closed. A by-ref payload binding INSIDE a variant is already rejected by the
                // `ByRef::No` gate below, so the discriminant-only slice needs no extra guard here.
                let pat_kind: &PatKind<'tcx> = if deref_scrut {
                    match &arm.pattern.kind {
                        PatKind::Deref { pin: rustc_hir::Pinnedness::Not, subpattern } => {
                            &subpattern.kind
                        }
                        PatKind::Wild => &arm.pattern.kind,
                        PatKind::Binding { .. } => {
                            return ArmClass::Reject("EnumMatch(ref binding arm)");
                        }
                        _ => return ArmClass::Reject("EnumMatch(ref arm not a deref pattern)"),
                    }
                } else {
                    &arm.pattern.kind
                };
                match pat_kind {
                    PatKind::Wild if arm_guard.is_some() => {
                        ArmClass::Reject("EnumMatch(guarded wildcard arm)")
                    }
                    PatKind::Wild => ArmClass::Wild(arm.body),
                    PatKind::Variant { variant_index, subpatterns, .. } => {
                        let vidx = variant_index.as_usize();
                        let Some(vfields) = variant_field_tys.get(vidx) else {
                            return ArmClass::Reject("EnumMatch(variant index OOB)");
                        };
                        let mut binds: Vec<(LocalVarId, u32, Option<u64>)> = Vec::new();
                        for sp in subpatterns {
                            if (sp.field.as_u32() as usize) >= vfields.len() {
                                return ArmClass::Reject("EnumMatch(payload field OOB)");
                            }
                            match &sp.pattern.kind {
                                PatKind::Wild => {}
                                PatKind::Binding {
                                    var,
                                    mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                                    subpattern: None,
                                    ..
                                } => {
                                    // Trust (B3-2c E4): a UNIT payload binding fails
                                    // closed — a bound unit local would make VarRef
                                    // return Some for a unit read, breaking the
                                    // producer-wide wave-UV value-less-unit invariant.
                                    // Parity-neutral: the legacy wave-EZ lane rejected
                                    // the same shape.
                                    if matches!(
                                        vfields.get(sp.field.as_u32() as usize),
                                        Some(Ty::Unit)
                                    ) {
                                        return ArmClass::Reject("EnumMatch(zst payload binding)");
                                    }
                                    binds.push((*var, sp.field.as_u32(), None))
                                }
                                // Trust (wave-L4G): a by-REF payload binding in the DEREF case
                                // (`match r:&E { V(x) => .. }` where `x: &FieldTy` via match
                                // ergonomics — as derived `Clone`/`Debug` emit for a heterogeneous
                                // enum routed here). The general-model twin of wave-L4: reconstruct
                                // `&field` as a flat-I8 interior GEP of the scrutinee ptr at the
                                // field's REAL rustc byte-offset `layout.for_variant(vidx)
                                // .fields.offset(field)` (the `place.rs` project_downcast+field
                                // composition). CONCRETE ONLY: param/infer/opaque enums are rejected
                                // before `layout_of`, so a wrong/absent offset is NEVER emitted.
                                // A non-thin `&str`/`&[U]`/`&dyn` field-ref fails closed (map_ty
                                // would drop its len/vtable through a thin `Ty::Ptr`).
                                PatKind::Binding {
                                    var,
                                    ty: bind_ty,
                                    mode: rustc_hir::BindingMode(rustc_hir::ByRef::Yes(..), _),
                                    subpattern: None,
                                    ..
                                } if deref_scrut => {
                                    let te = ty::TypingEnv::fully_monomorphized();
                                    let ptr_thin = match bind_ty.kind() {
                                        ty::Ref(_, pointee, _) => pointee.is_sized(tcx, te),
                                        _ => false,
                                    };
                                    if !ptr_thin {
                                        return ArmClass::Reject(
                                            "EnumMatch(ref payload non-thin binding)",
                                        );
                                    }
                                    if !layout_query_is_reentrant_safe(map_from) {
                                        return ArmClass::Reject(
                                            "EnumMatch(ref payload non-concrete enum)",
                                        );
                                    }
                                    let Ok(layout) = tcx.layout_of(te.as_query_input(map_from))
                                    else {
                                        return ArmClass::Reject(
                                            "EnumMatch(ref payload layout error)",
                                        );
                                    };
                                    let cx = ty::layout::LayoutCx::new(tcx, te);
                                    let off = layout
                                        .for_variant(&cx, *variant_index)
                                        .fields
                                        .offset(sp.field.as_u32() as usize)
                                        .bytes();
                                    binds.push((*var, sp.field.as_u32(), Some(off)));
                                }
                                // Trust (B3-2c E4): the `()` pattern on a UNIT field
                                // (`Ok(())` in a match arm) is IRREFUTABLE and binds
                                // NOTHING — a pure no-op field, the wave-NS precedent
                                // (no test, no bind, no ExtractField; byte-identical
                                // to `_`). Gate on the DEF field ty (the admission
                                // invariant), matching only the binds-nothing leaf
                                // shapes: an empty Leaf (`()`, a unit-struct pattern)
                                // or an empty Tuple pattern.
                                PatKind::Leaf { subpatterns }
                                    if subpatterns.is_empty()
                                        && matches!(
                                            vfields.get(sp.field.as_u32() as usize),
                                            Some(Ty::Unit)
                                        ) => {}
                                // other by-ref / `@` / nested / literal payload patterns — not modeled.
                                _ => {
                                    return ArmClass::Reject(
                                        "EnumMatch(non-binding payload subpattern)",
                                    );
                                }
                            }
                        }
                        ArmClass::Variant(vidx, binds, arm_guard, arm.body)
                    }
                    // Trust (wave-OR2): a niladic OR-pattern arm `E::A | E::B => body` on a
                    // first-class `Ty::Enum` (guards are already globally rejected above; a deref
                    // scrutinee is out via `!deref_scrut`). Mirrors the legacy `VariantOr`: EVERY
                    // alternative a `PatKind::Variant` whose payload binds nothing (empty subpatterns
                    // OR all `PatKind::Wild` — a binding/literal/nested subpattern fails closed),
                    // collected as variant INDICES (bounds-checked against `variant_field_tys`). A
                    // wrong routing is caught by the derived-MIR comparator (these general-path bodies
                    // are non-differential today, so this is clean-rate only).
                    PatKind::Or { pats } if !deref_scrut => {
                        let mut vidxs: Vec<usize> = Vec::with_capacity(pats.len());
                        for p in pats.iter() {
                            match &p.kind {
                                PatKind::Variant { variant_index, subpatterns, .. } => {
                                    let vidx = variant_index.as_usize();
                                    if variant_field_tys.get(vidx).is_none() {
                                        return ArmClass::Reject("EnumMatch(variant index OOB)");
                                    }
                                    let binds_nothing = subpatterns.is_empty()
                                        || subpatterns
                                            .iter()
                                            .all(|sp| matches!(sp.pattern.kind, PatKind::Wild));
                                    if !binds_nothing {
                                        return ArmClass::Reject(
                                            "EnumMatch(or-pattern alternative binds payload)",
                                        );
                                    }
                                    vidxs.push(vidx);
                                }
                                _ => {
                                    return ArmClass::Reject(
                                        "EnumMatch(or-pattern non-niladic-variant alternative)",
                                    );
                                }
                            }
                        }
                        if vidxs.is_empty() {
                            return ArmClass::Reject("EnumMatch(empty or-pattern)");
                        }
                        if arm_guard.is_some() {
                            ArmClass::Reject("EnumMatch(guarded or-pattern arm)")
                        } else {
                            ArmClass::VariantOr(vidxs, arm.body)
                        }
                    }
                    // binding-to-whole-enum / leaf / range / or / deref / slice → not modeled.
                    _ => ArmClass::Reject("EnumMatch(unsupported pattern)"),
                }
            })
            .collect();

        let mut variant_arms: Vec<(
            usize,
            Vec<(LocalVarId, u32, Option<u64>)>,
            Option<ExprId>,
            ExprId,
        )> = Vec::new();
        let mut wild_body: Option<ExprId> = None;
        for class in classes {
            match class {
                ArmClass::Reject(why) => {
                    self.unsupported.push((format!("{span:?}"), why));
                    return None;
                }
                ArmClass::Wild(body) => {
                    if wild_body.is_some() {
                        self.unsupported
                            .push((format!("{span:?}"), "EnumMatch(multiple wildcards)"));
                        return None;
                    }
                    wild_body = Some(body);
                }
                ArmClass::Variant(v, b, guard, body) => {
                    if wild_body.is_some() {
                        self.unsupported
                            .push((format!("{span:?}"), "EnumMatch(arm after wildcard)"));
                        return None;
                    }
                    variant_arms.push((v, b, guard, body));
                }
                // Trust (wave-OR2): expand a niladic OR-pattern arm into one no-binding `Variant`
                // entry per alternative variant index, all routing to the SHARED body. DEDUP here is
                // LOAD-BEARING (unlike the legacy path, the general case-build does NOT dedup — a
                // repeated index would mint a duplicate SwitchCase); a first-appearance keeps.
                ArmClass::VariantOr(vs, body) => {
                    if wild_body.is_some() {
                        self.unsupported
                            .push((format!("{span:?}"), "EnumMatch(arm after wildcard)"));
                        return None;
                    }
                    let mut seen: std::collections::HashSet<usize> =
                        std::collections::HashSet::new();
                    for v in vs {
                        if seen.insert(v) {
                            variant_arms.push((v, Vec::new(), None, body));
                        }
                    }
                }
            }
        }
        if variant_arms.is_empty() && wild_body.is_none() {
            self.unsupported.push((format!("{span:?}"), "EnumMatch(no arms)"));
            return None;
        }

        // 2. Lower the scrutinee, then extract its tag ONCE in the predecessor (canonical tag
        //    type — see the doc). Payload extraction is deferred to the arm blocks.
        let scrut_val0 = match self.lower_expr(scrutinee) {
            Some(v) => v,
            None => {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(scrutinee unsupported)"));
                return None;
            }
        };
        // Trust (wave-MR2): in the deref case the scrutinee lowered to a LEDGER-registered borrow
        // pointer — `Load` the pointee Ty::Enum value ONCE (a whole-aggregate Load, the wave-5/11
        // memory foothold; the comparator fail-closes Ty::Enum so this never flips), then the tag
        // `ExtractField` below reads it identically to the by-value path. The by-value path is
        // unchanged (a borrow-ptr scrutinee `match *r` is still out of scope there).
        let scrut_val = if deref_scrut {
            if !self.is_borrow_ptr(scrut_val0) {
                self.unsupported.push((
                    format!("{span:?}"),
                    "EnumMatch(ref scrutinee not a registered borrow)",
                ));
                return None;
            }
            let loaded = self.fresh();
            self.push_node(InstrNode::new(Inst::Load {
                    ty: Ty::Enum(eid),
                    ptr: scrut_val0,
                    volatile: false,
                    align: None,
                })
                .with_result(loaded),
            );
            loaded
        } else {
            if self.is_borrow_ptr(scrut_val0) {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(scrutinee is borrow ptr)"));
                return None;
            }
            scrut_val0
        };
        let tag_val = self.fresh();
        self.push_node(InstrNode::new(Inst::ExtractField { ty: tag_ty, aggregate: scrut_val, field: 0 })
                .with_result(tag_val),
        );

        // 3. Join shape (mirrors `lower_enum_match` step 3): unit → zero-param join.
        let result_ty = self.map_ty(result_rty);
        let value_producing = !matches!(result_ty, Ty::Unit);

        // 4. Choose the Switch default (mirrors step 4): a `_` arm, else the LAST variant arm
        //    of the exhaustive match (its case would be redundant).
        let default_arm: (Vec<(LocalVarId, u32, Option<u64>)>, Option<usize>, ExprId);
        let case_arms: Vec<(usize, Vec<(LocalVarId, u32, Option<u64>)>, Option<ExprId>, ExprId)>;
        match wild_body {
            Some(wb) => {
                default_arm = (Vec::new(), None, wb);
                case_arms = variant_arms;
            }
            None => {
                let mut va = variant_arms;
                let last = match va.pop() {
                    Some(a) => a,
                    None => {
                        self.unsupported.push((format!("{span:?}"), "EnumMatch(no default arm)"));
                        return None;
                    }
                };
                // Trust (B3-2b G1): a GUARDED arm can never be the exhaustive default — a
                // failed guard would have no fallback (Rust places the unguarded catch-all
                // last, so this is unreachable for valid Rust; fail closed defensively). The
                // legacy path's identical guard (lib.rs "guarded arm as exhaustive default").
                if last.2.is_some() {
                    self.unsupported.push((
                        format!("{span:?}"),
                        "EnumMatch(guarded arm as exhaustive default)",
                    ));
                    return None;
                }
                default_arm = (last.1, Some(last.0), last.3);
                case_arms = va;
            }
        }

        // 5. Blocks: one per case arm, one default, one join. Each case carries its variant's
        //    EXPLICIT discriminant value (fail-closed on a ledger desync).
        // Trust (B3-2b G1): each arm gets a Switch-target ENTRY block; a GUARDED arm
        // additionally gets a distinct BODY block (`Some(body_blk)`) — its entry is a
        // guard-test that CondBrs true->body, false->the guard-false route. An unguarded
        // arm's entry IS its body (`None`), byte-identical to the pre-G1 lowering.
        let mut case_blocks: Vec<(
            i128,
            BlockId,
            Option<BlockId>,
            usize,
            Vec<(LocalVarId, u32, Option<u64>)>,
            Option<ExprId>,
            ExprId,
        )> = Vec::with_capacity(case_arms.len());
        for (vidx, binds, guard, body) in case_arms {
            let Some(disc) = discriminants.get(vidx).copied().flatten() else {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(missing discriminant)"));
                return None;
            };
            let entry = self.fresh_block_id();
            let body_blk = guard.map(|_| self.fresh_block_id());
            case_blocks.push((disc, entry, body_blk, vidx, binds, guard, body));
        }
        let default_id = self.fresh_block_id();
        let join_id = self.fresh_block_id();

        // 6. Seal the predecessor with the `Switch` on the tag. ONE case per DISTINCT discriminant
        //    (first-appearance order) — a later same-discriminant arm (a CROSS-arm OR overlap like
        //    `A | B => x, B | C => y`, or a duplicate single-variant arm `A => x, A => y`, both of
        //    which rustc only WARNS as `unreachable_patterns` and KEEPS in THIR) is already covered
        //    by the first arm's block, so it mints no duplicate Switch case. Trust (wave-OR2 fix):
        //    mirrors `lower_enum_match` step 6 (`seen_discr` at ~11003) — the per-OR-arm dedup above
        //    only catches INTRA-arm dupes (`A | A | B`); WITHOUT this case-build dedup a duplicate
        //    `Constant::Int(d)` case is malformed IR, and these general-path bodies are
        //    non-differential (NotRun) so there is NO comparator backstop to catch it.
        let mut seen_discr: std::collections::HashSet<i128> = std::collections::HashSet::new();
        let cases: Vec<SwitchCase> = case_blocks
            .iter()
            .filter(|&&(d, _, _, _, _, _, _)| seen_discr.insert(d))
            .map(|&(d, entry, _, _, _, _, _)| SwitchCase {
                value: Constant::Int(d),
                target: entry,
                args: vec![],
            })
            .collect();
        self.seal_with(Inst::Switch {
            value: tag_val,
            default: default_id,
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        });

        // 7. Lower each arm (cases then default) with the SAME deferred-`Br` join merge as
        //    `lower_enum_match`. Payload bindings extract inside the arm's block; each bound
        //    local is a fresh per-arm `LocalVarId`, never part of the cross-join merge.
        let pre_locals = self.locals.clone();
        let mut captured: Vec<CapturedArm> = Vec::new();
        for (i, &(discr, entry, body_blk, vidx, ref binds, guard, body)) in
            case_blocks.iter().enumerate()
        {
            // Trust (B3-2b G1): a GUARDED arm — lower its guard-test block first (ported
            // from the legacy path). Bind the payload (so `V(x) if g` reads `x`), lower the
            // guard, and CondBr true->body, false->the guard-FALSE route: the NEXT arm in
            // source order sharing this discriminant (same-variant fallthrough
            // `V(x) if g => .., V(_) => ..`), else the default. A guard that reassigns an
            // OUTER local has no param-merge path from its successors (body/false) -> fail
            // closed. The body block re-binds (redundant, sound — same dominating scrut_val).
            if let Some(g) = guard {
                let body_blk = body_blk.expect("guarded arm has a body block");
                let false_id = match case_blocks[i + 1..]
                    .iter()
                    .find(|&&(dd, _, _, _, _, _, _)| dd == discr)
                {
                    Some(&(_, next_entry, _, _, _, _, _)) => next_entry,
                    None => {
                        // No same-variant successor: the guard-false lands on the default.
                        // Sound iff the default catches this discriminant — the wildcard
                        // (default_vidx None) or a popped same-variant catch-all
                        // (default_vidx == Some(vidx)). A different-variant default means a
                        // failed guard has no fallback (non-exhaustive; impossible for valid
                        // Rust) -> fail closed.
                        if default_arm.1.is_some() && default_arm.1 != Some(vidx) {
                            self.unsupported.push((
                                format!("{span:?}"),
                                "EnumMatch(guarded arm no same-variant fallback)",
                            ));
                        }
                        default_id
                    }
                };
                self.locals = pre_locals.clone();
                self.start_block(entry, vec![]);
                if !self.bind_enum_payload_general(
                    span,
                    vidx,
                    binds,
                    scrut_val0,
                    scrut_val,
                    &variant_field_tys,
                ) {
                    self.seal_with(Inst::Unreachable);
                    // Bind failure already pushed a tag. The guarded entry is now
                    // an `Unreachable` sink, so its reserved body block has no
                    // predecessor and is intentionally not emitted.
                    continue;
                }
                // Snapshot AFTER binding the (fresh, per-arm) payload local so the reassign
                // check flags only guard SIDE EFFECTS, not the payload binding.
                let guard_base = self.locals.clone();
                let gv = match self.lower_expr(g) {
                    Some(v) => v,
                    None => {
                        self.unsupported
                            .push((format!("{span:?}"), "EnumMatch(guard unsupported)"));
                        if !self.sealed {
                            self.seal_with(Inst::Unreachable);
                        }
                        continue;
                    }
                };
                self.seal_with(Inst::CondBr {
                    cond: gv,
                    then_target: body_blk,
                    then_args: vec![],
                    else_target: false_id,
                    else_args: vec![],
                });
                if locals_changed(&guard_base, &self.locals) {
                    self.unsupported
                        .push((format!("{span:?}"), "EnumMatch(guard reassigns local)"));
                }
            }
            // Emit the arm BODY: an unguarded arm's entry IS its body; a guarded arm's body
            // is the distinct body block the guard-test CondBrs into.
            let body_target = body_blk.unwrap_or(entry);
            self.locals = pre_locals.clone();
            captured.push(self.lower_enum_match_arm_general(
                span,
                value_producing,
                body_target,
                vidx,
                binds,
                scrut_val0,
                scrut_val,
                &variant_field_tys,
                body,
                "EnumMatch(case arm no value)",
            ));
        }
        self.locals = pre_locals.clone();
        let (default_binds, default_vidx, default_body) = default_arm;
        captured.push(match default_vidx {
            Some(vidx) => self.lower_enum_match_arm_general(
                span,
                value_producing,
                default_id,
                vidx,
                &default_binds,
                scrut_val0,
                scrut_val,
                &variant_field_tys,
                default_body,
                "EnumMatch(default arm no value)",
            ),
            // A `_` default binds nothing (no variant to project from).
            None => {
                self.start_block(default_id, vec![]);
                let val = self.lower_expr(default_body);
                self.capture_arm(span, value_producing, val, "EnumMatch(default arm no value)")
            }
        });

        // 8. Merge at the join (mirrors `lower_enum_match` step 8 exactly).
        let any_reaches_join = captured.iter().any(|a| a.is_reaching());
        if !any_reaches_join {
            self.locals = pre_locals;
            return None;
        }
        let arm_refs: Vec<&CapturedArm> = captured.iter().collect();
        let merged: Vec<(LocalVarId, Ty)> = self.merged_locals(&pre_locals, &arm_refs);
        let join_param = if value_producing { Some(self.fresh()) } else { None };
        let merged_params: Vec<(ValueId, Ty)> =
            merged.iter().map(|(_, ty)| (self.fresh(), ty.clone())).collect();
        for arm in captured {
            self.seal_arm_into_join(arm, join_id, join_param.is_some(), &pre_locals, &merged);
        }
        let mut join_params: Vec<(ValueId, Ty)> = Vec::new();
        if let Some(r) = join_param {
            join_params.push((r, result_ty));
        }
        join_params.extend(merged_params.iter().cloned());
        self.locals = pre_locals;
        self.start_block(join_id, join_params);
        for ((var, ty), (param, _)) in merged.iter().zip(merged_params.iter()) {
            self.set_local(*var, *param, ty.clone());
        }
        join_param
    }

    /// Lower one GENERAL-enum `match` arm into block `blk`: `ExtractField` each bound payload
    /// slot (`1 + field_index`, typed with the variant's OWN field type — the slot only exists
    /// under this arm's `Switch` case, which is why extraction happens here and not in the
    /// predecessor), bind it, lower the body, and CAPTURE the arm for the deferred-`Br` join
    /// merge (mirrors `lower_enum_match_arm`).
    #[allow(clippy::too_many_arguments)]
    fn lower_enum_match_arm_general(
        &mut self,
        span: rustc_span::Span,
        value_producing: bool,
        blk: BlockId,
        vidx: usize,
        binds: &[(LocalVarId, u32, Option<u64>)],
        scrut_val0: ValueId,
        scrut_val: ValueId,
        variant_field_tys: &[Vec<Ty>],
        body: ExprId,
        label: &'static str,
    ) -> CapturedArm {
        self.start_block(blk, vec![]);
        if !self.bind_enum_payload_general(
            span,
            vidx,
            binds,
            scrut_val0,
            scrut_val,
            variant_field_tys,
        ) {
            return self.capture_arm(span, value_producing, None, label);
        }
        let val = self.lower_expr(body);
        self.capture_arm(span, value_producing, val, label)
    }

    /// Trust (B3-2b G1): bind a first-class enum arm's payload locals into the CURRENT
    /// block — factored out of `lower_enum_match_arm_general` so a GUARDED arm's
    /// guard-test block can bind the payload (`V(x) if g` reading `x`) before evaluating
    /// the guard, then the body block re-binds (redundant, sound — same dominating
    /// `scrut_val`). Returns `false` on a classification/variant desync (the caller
    /// fail-closes the arm). Byte-identical binding to the pre-G1 inline loop.
    fn bind_enum_payload_general(
        &mut self,
        span: rustc_span::Span,
        vidx: usize,
        binds: &[(LocalVarId, u32, Option<u64>)],
        scrut_val0: ValueId,
        scrut_val: ValueId,
        variant_field_tys: &[Vec<Ty>],
    ) -> bool {
        for (var, field_idx, off) in binds {
            // Classification bounds-checked the index against THIS variant (checked, not
            // assumed — a desync here would mint an ill-typed extract).
            let Some(field_ty) =
                variant_field_tys.get(vidx).and_then(|f| f.get(*field_idx as usize))
            else {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(binding field desync)"));
                return false;
            };
            let field_ty = field_ty.clone();
            // Trust (B3-2c E4, belt-and-suspenders): the classifier rejects unit
            // payload bindings; reaching one here is a desync — fail the arm closed.
            if matches!(field_ty, Ty::Unit) {
                self.unsupported.push((format!("{span:?}"), "EnumMatch(zst payload binding)"));
                return false;
            }
            match off {
                // By-VALUE binding (`None` offset) — `ExtractField` the field from the loaded
                // in-register aggregate (slot `1 + field_index`, the variant's own field type).
                // Byte-identical to the pre-L4G path.
                None => {
                    let bound = self.fresh();
                    self.push_node(InstrNode::new(Inst::ExtractField {
                            ty: field_ty.clone(),
                            aggregate: scrut_val,
                            field: 1 + *field_idx,
                        })
                        .with_result(bound),
                    );
                    self.set_local(*var, bound, field_ty);
                }
                // Trust (wave-L4G): by-REF binding (`Some(off)`) — reconstruct `&field` as a flat-I8
                // interior GEP of the scrutinee borrow pointer `scrut_val0` at the field's real rustc
                // byte-offset `off` (computed at classify), exactly wave-L4's / wave-25b's machinery.
                // `borrow_ptrs` (all non-return escape guards fail closed) + `interior_ptrs` (only
                // when `scrut_val0` is a ref-PARAMETER ptr -> return-escape aliases outliving caller
                // memory). The bound local is a thin `Ty::Ptr` (the field is a Sized scalar/thin ref).
                Some(off) => {
                    let off_val = self.fresh();
                    self.push_node(InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(*off as i128),
                        })
                        .with_result(off_val),
                    );
                    let iptr = self.fresh();
                    self.push_node(InstrNode::new(Inst::GEP {
                            pointee_ty: Ty::I8,
                            base: scrut_val0,
                            indices: vec![off_val],
                            inbounds: true,
                        })
                        .with_result(iptr),
                    );
                    self.borrow_ptrs.push(iptr);
                    if self.ref_param_ptrs.contains(&scrut_val0) {
                        self.interior_ptrs.push(iptr);
                    }
                    self.set_local(*var, iptr, Ty::Ptr);
                }
            }
        }
        true
    }

    /// Lower `loop { body }` (the desugaring target of `while c {b}` and a `loop`) into a header
    /// block + back-edge + exit block, with the loop-carried locals threaded as header block-params —
    /// the SAME SSA-with-block-param merge `lower_if` uses, generalized to a back-edge:
    ///
    /// ```text
    ///   pre:    <init…>  br header(<initial carried values>)
    ///   header: (params: [%c0 : T0, %c1 : T1, …])  <body…>  br header(<current carried values>)
    ///                                                       (the BACK-EDGE — body fallthrough)
    ///   exit:   ()  <continues; carried locals readable = header params>
    /// ```
    ///
    /// `break` (no value) routes to `exit`; `continue` routes back to `header` (both via the loop
    /// stack). The interpreter executes the back-edge as a `Step::Jump` to the earlier header block
    /// and rebinds its params from the `Br` args each iteration, bounded by fuel — exactly a loop.
    ///
    /// DATAFLOW after the loop: a carried local's value is its HEADER block-param. A `while`'s
    /// condition-false `break` carries the header values unchanged into `exit`, so the post-loop value
    /// of every carried local is precisely its header param — which is what the carried local is bound
    /// to throughout the header. We therefore leave the carried bindings at their header-param versions
    /// when opening `exit`.
    ///
    /// FAIL-CLOSED: a NESTED loop (one already on the stack), a carried local with no recorded `Ty`
    /// (cannot type its header param), or any unsupported shape inside the body (records its own
    /// `unsupported`). `break`-with-value and labeled break/continue fail closed in their own arms.
    fn lower_loop(
        &mut self,
        span: rustc_span::Span,
        loop_scope: region::Scope,
        body: ExprId,
    ) -> Option<ValueId> {
        // Single-loop scope for now: a nested loop would need the carried-local merge to compose
        // across two headers (and break/continue to pick the right level). Fail closed rather than
        // force it — the loop stack is kept so this is a clean future extension.
        if !self.loop_stack.is_empty() {
            self.unsupported.push((format!("{span:?}"), "Loop(nested)"));
            return None;
        }

        // 1. Loop-carried locals: every local assigned anywhere in `body`, in stable first-seen order,
        //    that is currently bound (a pre-loop `let`) and has a recorded `Ty`. A carried local not
        //    bound before the loop, or without a type, fails closed (we cannot seed/type its param).
        let assigned = self.collect_assigned_locals(body);
        let mut carried_init: Vec<(LocalVarId, ValueId, Ty)> = Vec::new();
        for var in assigned {
            // Trust: a PROMOTED local is memory-backed (its assignments are `Store`s, its reads
            // `Load`s) — it is NOT SSA, so it must NOT become a loop-carried block-param. Its memory
            // slot already threads the value across iterations (the same slot is read/written each
            // pass). Skip it here so the SSA merge never double-handles it (it isn't in `locals`,
            // and `local_value` would be `None`, which would otherwise fail the loop closed).
            if self.is_promoted(var) {
                continue;
            }
            let init = match self.local_value(var) {
                Some(v) => v,
                None => {
                    // Assigned-but-unbound-before-the-loop: e.g. `let x; while … { x = … }`. We have no
                    // initial value to seed the header param with. Fail closed.
                    self.unsupported
                        .push((format!("{span:?}"), "Loop(carried local unbound pre-loop)"));
                    return None;
                }
            };
            let ty = match self.local_ty(var) {
                Some(t) => t,
                None => {
                    self.unsupported.push((format!("{span:?}"), "Loop(carried local untyped)"));
                    return None;
                }
            };
            carried_init.push((var, init, ty));
        }

        // 2. Allocate header + exit. The header gets one fresh block-param ValueId per carried local.
        let header_id = self.fresh_block_id();
        let exit_id = self.fresh_block_id();
        let header_params: Vec<(ValueId, Ty)> =
            carried_init.iter().map(|(_, _, ty)| (self.fresh(), ty.clone())).collect();

        // 3. Seal the pre-loop block with the entry `Br` to the header, passing each carried local's
        //    INITIAL (pre-loop) value as the matching header-param arg.
        let init_args: Vec<ValueId> = carried_init.iter().map(|(_, init, _)| *init).collect();
        self.seal_with(Inst::Br { target: header_id, args: init_args });

        // 4. Open the header; rebind each carried local to its header block-param so uses inside the
        //    body (and the back-edge args) read the per-iteration version.
        self.start_block(header_id, header_params.clone());
        let carried: Vec<(LocalVarId, ValueId, Ty)> = carried_init
            .iter()
            .zip(header_params.iter())
            .map(|((var, _, ty), (param, _))| {
                self.set_local(*var, *param, ty.clone());
                (*var, *param, ty.clone())
            })
            .collect();

        // 5. Push the loop context so Break/Continue inside the body resolve. We need the loop's
        //    `region::Scope` label: an unlabeled `break`/`continue` inside `loop { … }` carries the
        //    loop body's enclosing scope. We capture it lazily from the FIRST break/continue we see
        //    (the scope is identical for all breaks of this loop), so seed with the body expr's scope
        //    proxy. Simpler + robust: store the carried set and match break/continue by "innermost".
        self.loop_stack.push(LoopCtx {
            scope: loop_scope,
            header: header_id,
            exit: exit_id,
            carried: carried.clone(),
        });

        // 6. Lower the body in the header block. Its result is discarded (loop body is unit-typed).
        let _ = self.lower_expr(body);

        // 7. Back-edge: if the body fell through (did not seal via `break`/`continue`/`return`), branch
        //    back to the header carrying each carried local's CURRENT value.
        if !self.sealed {
            let back_args: Vec<ValueId> = carried
                .iter()
                .map(|(var, param, _)| self.local_value(*var).unwrap_or(*param))
                .collect();
            self.seal_with(Inst::Br { target: header_id, args: back_args });
        }

        // 8. Pop the loop context and open the exit. Carried locals stay bound to their header params
        //    (the post-loop dataflow — see the method doc). The loop expression is unit (`None`).
        self.loop_stack.pop();
        self.start_block(exit_id, vec![]);
        for (var, param, ty) in &carried {
            self.set_local(*var, *param, ty.clone());
        }
        None
    }

    /// Lower `break` / `break 'l`. No-value `break` to the innermost loop → `Br` to its exit (the exit
    /// reads carried locals at their header-param versions). FAIL-CLOSED: `break value`, a labeled
    /// break not targeting the innermost loop, or a `break` outside any loop.
    fn lower_break(
        &mut self,
        span: rustc_span::Span,
        label: region::Scope,
        has_value: bool,
    ) -> Option<ValueId> {
        if has_value {
            self.unsupported.push((format!("{span:?}"), "Break(with value)"));
            return None;
        }
        let exit = match self.loop_stack.last() {
            Some(ctx) if ctx.scope == label => ctx.exit,
            Some(_) => {
                // Labeled break aimed at an outer loop (multi-level breakout) — not modeled.
                self.unsupported.push((format!("{span:?}"), "Break(non-innermost label)"));
                return None;
            }
            None => {
                self.unsupported.push((format!("{span:?}"), "Break(outside loop)"));
                return None;
            }
        };
        self.seal_with(Inst::Br { target: exit, args: vec![] });
        None
    }

    /// Lower `continue` / `continue 'l` → `Br` (back-edge) to the innermost loop's header, carrying the
    /// loop-carried locals' current values. FAIL-CLOSED: a labeled continue not targeting the innermost
    /// loop, or a `continue` outside any loop.
    fn lower_continue(&mut self, span: rustc_span::Span, label: region::Scope) -> Option<ValueId> {
        // Clone the innermost ctx's header + carried set (a copy avoids borrowing `self` across the
        // `local_value`/`seal_with` mutations below).
        let (header, carried): (BlockId, Vec<(LocalVarId, ValueId)>) = match self.loop_stack.last()
        {
            Some(ctx) if ctx.scope == label => {
                (ctx.header, ctx.carried.iter().map(|(var, param, _)| (*var, *param)).collect())
            }
            Some(_) => {
                self.unsupported.push((format!("{span:?}"), "Continue(non-innermost label)"));
                return None;
            }
            None => {
                self.unsupported.push((format!("{span:?}"), "Continue(outside loop)"));
                return None;
            }
        };
        let args: Vec<ValueId> =
            carried.iter().map(|(var, param)| self.local_value(*var).unwrap_or(*param)).collect();
        self.seal_with(Inst::Br { target: header, args });
        None
    }

    /// Trust: the `region::Scope` an unlabeled `break`/`continue` inside `loop { body }` carries. The
    /// loop's break target scope is the loop expression's own node scope; we approximate it by reading
    /// the body expression's enclosing scope from any `Break`/`Continue` THIR node found in the body
    /// (they all carry the same loop label). Falls back to a scope derived from the body expr's HIR id
    /// when the body contains no break/continue (e.g. an infinite `loop {}` with only `return`) — in
    /// that case there is nothing to match against, so the exact value is irrelevant.
    fn loop_body_scope(&self, body: ExprId) -> region::Scope {
        // Find the first Break/Continue label reachable in the body (without descending into a nested
        // loop, whose breaks carry a different label). All breaks/continues of THIS loop share it.
        fn find(thir: &Thir<'_>, e: ExprId) -> Option<region::Scope> {
            match &thir.exprs[e].kind {
                ExprKind::Break { label, .. } | ExprKind::Continue { label } => Some(*label),
                ExprKind::Loop { .. } => None, // a nested loop's breaks belong to it, not us
                ExprKind::Scope { value, .. }
                | ExprKind::Use { source: value }
                | ExprKind::NeverToAny { source: value } => find(thir, *value),
                ExprKind::Block { block } => {
                    let blk = &thir.blocks[*block];
                    for s in blk.stmts.iter() {
                        if let StmtKind::Expr { expr, .. } = &thir.stmts[*s].kind {
                            if let Some(sc) = find(thir, *expr) {
                                return Some(sc);
                            }
                        }
                    }
                    blk.expr.and_then(|t| find(thir, t))
                }
                ExprKind::If { cond, then, else_opt, .. } => find(thir, *cond)
                    .or_else(|| find(thir, *then))
                    .or_else(|| else_opt.and_then(|e| find(thir, e))),
                _ => None,
            }
        }
        // Fallback: a loop body with no break/continue (e.g. an infinite `loop {}` whose only exit is
        // `return`). The scope value is never matched against anything in that case, so any sentinel is
        // fine — use `ItemLocalId::ZERO` to avoid fabricating a HIR id.
        find(self.thir, body).unwrap_or(region::Scope {
            local_id: rustc_hir::ItemLocalId::ZERO,
            data: region::ScopeData::Node,
        })
    }

    /// Trust: the set of locals ASSIGNED (`ExprKind::Assign` to a bare local) anywhere in `body`, in
    /// stable first-seen order — the loop-carried set that becomes the header's block-params. We
    /// descend through the body's expression tree but DO NOT recurse into a nested `Loop` (its carried
    /// locals are its own concern; a nested loop fails closed anyway in `lower_loop`). A `let`-declared
    /// local inside the body that is also reassigned is still collected, but `lower_loop` fails closed
    /// if it has no pre-loop binding — so only genuinely loop-carried (pre-existing) locals survive.
    fn collect_assigned_locals(&self, body: ExprId) -> Vec<LocalVarId> {
        let mut out: Vec<LocalVarId> = Vec::new();
        self.collect_assigned_into(body, &mut out);
        out
    }

    fn collect_assigned_into(&self, e: ExprId, out: &mut Vec<LocalVarId>) {
        match &self.thir.exprs[e].kind {
            ExprKind::Assign { lhs, rhs } => {
                if let Some(var) = self.place_local(*lhs) {
                    if !out.contains(&var) {
                        out.push(var);
                    }
                }
                self.collect_assigned_into(*rhs, out);
            }
            ExprKind::AssignOp { lhs, rhs, .. } => {
                // `x += e` also reassigns `x` (`lower_assign_op` rebinds it via `set_local`, the
                // same SSA rebind a plain `x = …` uses), so it is loop-carried exactly like Assign.
                if let Some(var) = self.place_local(*lhs) {
                    if !out.contains(&var) {
                        out.push(var);
                    }
                }
                self.collect_assigned_into(*rhs, out);
            }
            ExprKind::Scope { value, .. }
            | ExprKind::Use { source: value }
            | ExprKind::NeverToAny { source: value } => self.collect_assigned_into(*value, out),
            ExprKind::Block { block } => {
                let blk = &self.thir.blocks[*block];
                for s in blk.stmts.iter() {
                    match &self.thir.stmts[*s].kind {
                        StmtKind::Expr { expr, .. } => self.collect_assigned_into(*expr, out),
                        StmtKind::Let { initializer, .. } => {
                            if let Some(init) = initializer {
                                self.collect_assigned_into(*init, out);
                            }
                        }
                    }
                }
                if let Some(t) = blk.expr {
                    self.collect_assigned_into(t, out);
                }
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                self.collect_assigned_into(*cond, out);
                self.collect_assigned_into(*then, out);
                if let Some(e) = else_opt {
                    self.collect_assigned_into(*e, out);
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.collect_assigned_into(*scrutinee, out);
                for arm_id in arms.iter() {
                    self.collect_assigned_into(self.thir.arms[*arm_id].body, out);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
                self.collect_assigned_into(*lhs, out);
                self.collect_assigned_into(*rhs, out);
            }
            ExprKind::Unary { arg, .. } => self.collect_assigned_into(*arg, out),
            ExprKind::Call { args, .. } => {
                for a in args.iter() {
                    self.collect_assigned_into(*a, out);
                }
            }
            ExprKind::Return { value } => {
                if let Some(v) = value {
                    self.collect_assigned_into(*v, out);
                }
            }
            // A nested loop's assignments are its own (and it fails closed); do not descend.
            ExprKind::Loop { .. } => {}
            _ => {}
        }
    }

    /// Trust: PRE-PASS — the set of locals `&mut`-borrowed ANYWHERE in `body` (an
    /// `ExprKind::Borrow{ borrow_kind: Mut{..}, arg=&local }`), in stable first-seen order. These are
    /// the locals to PROMOTE to memory (a write through the pointer must be visible to later reads, so
    /// they cannot stay SSA). We descend the FULL expression tree — including nested loops, if/match
    /// arms, borrow/deref operands, binary/call operands, assignment rhs, tuple/struct fields — because
    /// a `&mut local` anywhere in the function forces promotion of that local for its whole lifetime.
    /// (Type-based promotability — only scalar locals are promotable — is enforced at the local's
    /// `let`/param site via `is_scalar_ty`; a non-scalar `&mut` local then fails closed there.)
    fn collect_mut_borrowed(&self, body: ExprId) -> Vec<LocalVarId> {
        let mut out: Vec<LocalVarId> = Vec::new();
        self.collect_mut_borrowed_into(body, &mut out);
        out
    }

    fn collect_mut_borrowed_into(&self, e: ExprId, out: &mut Vec<LocalVarId>) {
        match &self.thir.exprs[e].kind {
            ExprKind::Borrow { borrow_kind, arg } => {
                if matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }) {
                    if let Some(var) = self.place_local(*arg) {
                        if !out.contains(&var) {
                            out.push(var);
                        }
                    }
                }
                // Descend into the borrowed place too (e.g. `&mut *r` — though that fails closed at
                // lowering, collecting any inner `&mut local` keeps the set complete).
                self.collect_mut_borrowed_into(*arg, out);
            }
            ExprKind::Deref { arg } => self.collect_mut_borrowed_into(*arg, out),
            ExprKind::Assign { lhs, rhs } => {
                self.collect_mut_borrowed_into(*lhs, out);
                self.collect_mut_borrowed_into(*rhs, out);
            }
            ExprKind::AssignOp { lhs, rhs, .. } => {
                self.collect_mut_borrowed_into(*lhs, out);
                self.collect_mut_borrowed_into(*rhs, out);
            }
            ExprKind::Scope { value, .. }
            | ExprKind::Use { source: value }
            | ExprKind::NeverToAny { source: value } => self.collect_mut_borrowed_into(*value, out),
            ExprKind::Block { block } => {
                let blk = &self.thir.blocks[*block];
                for s in blk.stmts.iter() {
                    match &self.thir.stmts[*s].kind {
                        StmtKind::Expr { expr, .. } => self.collect_mut_borrowed_into(*expr, out),
                        StmtKind::Let { initializer, .. } => {
                            if let Some(init) = initializer {
                                self.collect_mut_borrowed_into(*init, out);
                            }
                        }
                    }
                }
                if let Some(t) = blk.expr {
                    self.collect_mut_borrowed_into(t, out);
                }
            }
            ExprKind::If { cond, then, else_opt, .. } => {
                self.collect_mut_borrowed_into(*cond, out);
                self.collect_mut_borrowed_into(*then, out);
                if let Some(e) = else_opt {
                    self.collect_mut_borrowed_into(*e, out);
                }
            }
            ExprKind::Match { scrutinee, arms, .. } => {
                self.collect_mut_borrowed_into(*scrutinee, out);
                for arm_id in arms.iter() {
                    self.collect_mut_borrowed_into(self.thir.arms[*arm_id].body, out);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } | ExprKind::LogicalOp { lhs, rhs, .. } => {
                self.collect_mut_borrowed_into(*lhs, out);
                self.collect_mut_borrowed_into(*rhs, out);
            }
            ExprKind::Unary { arg, .. } => self.collect_mut_borrowed_into(*arg, out),
            ExprKind::Field { lhs, .. } => self.collect_mut_borrowed_into(*lhs, out),
            ExprKind::Call { fun, args, .. } => {
                self.collect_mut_borrowed_into(*fun, out);
                for a in args.iter() {
                    self.collect_mut_borrowed_into(*a, out);
                }
            }
            ExprKind::Tuple { fields } => {
                for f in fields.iter() {
                    self.collect_mut_borrowed_into(*f, out);
                }
            }
            ExprKind::Adt(adt_expr) => {
                for f in adt_expr.fields.iter() {
                    self.collect_mut_borrowed_into(f.expr, out);
                }
            }
            ExprKind::Return { value } => {
                if let Some(v) = value {
                    self.collect_mut_borrowed_into(*v, out);
                }
            }
            // A `loop`'s body may `&mut`-borrow an outer local; descend (unlike the carried-locals
            // pre-pass, which scopes assignments to the current loop — here we want the WHOLE function).
            ExprKind::Loop { body } => self.collect_mut_borrowed_into(*body, out),
            _ => {}
        }
    }
}

/// Interpretable placeholder constant for a scalar field type, used to seed a runtime tuple
/// aggregate that `InsertField` then overwrites with the real field values. We seed with a typed
/// `Const` (never `Inst::Undef`, which the reference interpreter executes as eager UB) so the seed
/// aggregate is fully interpretable. `eval_insert_field` validates the seed's per-field types match
/// the inserted values, so each placeholder must carry its field's type: `Int(0)` for the integer
/// widths, `Bool(false)` for bools, `Float(0.0)` for f32/f64 (the interpreter's
/// `constant_to_value` materializes `(Ty::F32|F64, Constant::Float)` via `float_bits_from_f64` —
/// exact for `0.0` at both widths; f16 is NOT seedable, its constants are interpreter-refused).
/// Returns `None` (fail-closed) for any other field type — nested aggregates are out of scope
/// for now.
fn seed_constant(ty: &Ty) -> Option<Constant> {
    match ty {
        Ty::Bool => Some(Constant::Bool(false)),
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
        | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128
        // Trust (v25 B1): faithful scalars seed like their carriers — 0 is a
        // valid inhabitant of all three ('\0' is a Unicode scalar value).
        | Ty::Isize | Ty::Usize | Ty::Char => Some(Constant::Int(0)),
        Ty::F32 | Ty::F64 => Some(Constant::Float(0.0)),
        _ => None,
    }
}

/// Trust: the `#[repr(iN/uN/isize/usize)]` tag hint of an enum `AdtDef`, as the
/// `trust_ir::EnumTagRepr` the general-path `EnumDef` pins its tag lane with. Outer `None`
/// (fail-closed) ONLY for a hint the canonical tag cannot express (`repr(i128/u128)` — trust-ir
/// tags cap at 64 bits); `Some(None)` for no hint (the canonical layout then picks the smallest
/// width covering the effective discriminants — `EnumTagRepr::smallest_for`, the SAME rule the
/// pinned interpreter applies). Pointer-sized hints take the producer's uniform 64-bit collapse.
fn enum_repr_hint(adt: ty::AdtDef<'_>) -> Option<Option<trust_ir::EnumTagRepr>> {
    use rustc_abi::{Integer, IntegerType};
    use trust_ir::EnumTagRepr as R;
    Some(match adt.repr().int {
        None => None,
        Some(IntegerType::Pointer(signed)) => Some(if signed { R::I64 } else { R::U64 }),
        Some(IntegerType::Fixed(i, signed)) => Some(match (i, signed) {
            (Integer::I8, true) => R::I8,
            (Integer::I8, false) => R::U8,
            (Integer::I16, true) => R::I16,
            (Integer::I16, false) => R::U16,
            (Integer::I32, true) => R::I32,
            (Integer::I32, false) => R::U32,
            (Integer::I64, true) => R::I64,
            (Integer::I64, false) => R::U64,
            (Integer::I128, _) => return None,
        }),
    })
}

/// Trust: `(bit width, signed)` for a fixed-width integer `trust_ir::Ty`, or `None` for any
/// non-integer (bool/ptr/aggregate/unit). Drives the integer-cast `CastOp` choice (`Trunc`/`ZExt`/
/// `SExt`) in the `ExprKind::Cast` arm. Bool is excluded HERE (it is not a fixed-width int), but
/// `bool as uN/iN` is still lowered by that arm as a dedicated `ZExt` case — see `float_scalar_bits`
/// and the arm doc for the full int/bool/float cast classification.
pub(crate) fn int_scalar_bits(ty: &Ty) -> Option<(u32, bool)> {
    Some(match ty {
        // Trust (v25 B1): faithful scalars at the pinned 64-bit target;
        // char's carrier is 32-bit unsigned (its Unicode range is the
        // validator's claim, not a width property).
        Ty::Isize => (64, true),
        Ty::Usize => (64, false),
        Ty::Char => (32, false),
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        Ty::U128 => (128, false),
        _ => return None,
    })
}

/// Trust: the bit width of an IEEE-754 float `trust_ir::Ty` (`f32`→32, `f64`→64), or `None`
/// for any non-float. Companion to `int_scalar_bits`; drives the float-cast `CastOp` choice
/// (`FPExt`/`FPTrunc` for float→float, `SIToFP`/`UIToFP` for int→float) in the `ExprKind::Cast`
/// arm. NB float→int is NOT driven from here — it stays fail-closed (`Cast(float→int
/// saturating)`) because Rust's `as` from float to int saturates + maps NaN→0 while trust-ir's
/// `FPToSI/FPToUI` are documented LLVM-raw (non-saturating; `interpret.rs` numerics §2).
fn float_scalar_bits(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::F32 => Some(32),
        Ty::F64 => Some(64),
        _ => None,
    }
}

/// Trust: the MINIMUM value of a SIGNED fixed-width integer `trust_ir::Ty`, as the `i128` a
/// `Constant::Int` carries — the `MIN` operand of the unconditional signed `MIN / -1` division-
/// overflow assert (mirroring MIR's `minval_literal`). `None` for any non-signed-int type
/// (the caller only asks for signed operands; this is the defensive fail-closed arm).
fn int_min_value(ty: &Ty) -> Option<i128> {
    Some(match ty {
        // Trust (v25 B1): isize MIN at the 64-bit reference width.
        Ty::Isize => i64::MIN as i128,
        Ty::I8 => i8::MIN as i128,
        Ty::I16 => i16::MIN as i128,
        Ty::I32 => i32::MIN as i128,
        Ty::I64 => i64::MIN as i128,
        Ty::I128 => i128::MIN,
        _ => return None,
    })
}

/// Trust: the UNSIGNED same-width twin of a fixed-width integer `trust_ir::Ty` — the type MIR's
/// shift-amount check casts a signed shift amount to (`IntToInt` to `int_width.to_unsigned()`,
/// as_rvalue.rs:485-499) before the `amount < BITS` comparison. Unsigned types map to themselves;
/// `None` for any non-integer (defensive fail-closed).
fn unsigned_twin(ty: &Ty) -> Option<Ty> {
    Some(match ty {
        Ty::I8 => Ty::U8,
        Ty::I16 => Ty::U16,
        Ty::I32 => Ty::U32,
        Ty::I64 => Ty::U64,
        Ty::I128 => Ty::U128,
        // Trust (v25 B1): pointer-width twins; char is NOT an arithmetic
        // int (no shift-amount role) — falls to None (fail closed).
        Ty::Isize => Ty::Usize,
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 | Ty::Usize => ty.clone(),
        _ => return None,
    })
}

/// Trust (RPIT cycle fix): pre-borrowck demand guards.
///
/// The THIR→trust-ir lowering runs INSIDE `mir_built` (the builder/mod.rs hook)
/// — BEFORE borrowck of the body being lowered. A type that still mentions an
/// UNREVEALED opaque (`impl Trait` of this — or any not-yet-borrowck'd — body)
/// must not be fed to `layout_of`/`needs_drop`/`try_normalize_erasing_regions`/
/// `type_is_copy_modulo_regions` under the revealing
/// `TypingEnv::fully_monomorphized()`: the reveal demands `type_of(opaque)` →
/// borrowck of the defining body → `mir_built` of that body — the very query in
/// progress — a FATAL query cycle (E0391), not the recoverable `LayoutError`
/// the fail-closed call sites assume. These wrappers make the documented "errs
/// on opaque → fail closed" semantics real by refusing the demand up front (an
/// O(1) type-flags check). Post-borrowck callers (the flip path, after
/// RevealAll) see no opaques, so the wrappers are transparent there.
pub(crate) fn cycle_safe_layout_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    te: ty::TypingEnv<'tcx>,
    ty: RustcTy<'tcx>,
) -> Option<ty::layout::TyAndLayout<'tcx>> {
    if !layout_query_is_reentrant_safe(ty) {
        return None;
    }
    tcx.layout_of(te.as_query_input(ty)).ok()
}

/// Trust (B3-3): map a rustc enum layout onto trust-ir's
/// [`trust_ir::EnumLayoutDescriptor`], or decline (`None`) when the layout is
/// not expressible in the v31 grammar. LOCKSTEP MIRROR of the oracle chain
/// (extractor `extractor_enum_layout_info` + bridge canonical-width gate) —
/// keep the decline set identical on both sides:
/// * `Variants::Single`/`Empty` — no tag lane to describe;
/// * a tag/niche scalar that is not a mappable integer (float or i128;
///   `Pointer` pins to U64 on the 64-bit reference target);
/// * Direct whose rustc tag scalar disagrees with the def's CANONICAL tag
///   repr — the descriptor's Direct tag lane is normatively sized at
///   canonical width, so a rustc-widened tag must not mint a wrong claim.
fn producer_enum_layout_descriptor<'tcx>(
    def: &trust_ir::EnumDef,
    adt: ty::AdtDef<'tcx>,
    l: &ty::layout::TyAndLayout<'tcx>,
) -> Option<trust_ir::EnumLayoutDescriptor> {
    use rustc_abi::{Integer, Primitive, TagEncoding, Variants};
    let repr_of_scalar = |s: rustc_abi::Scalar| -> Option<trust_ir::EnumTagRepr> {
        use trust_ir::EnumTagRepr as R;
        Some(match s.primitive() {
            Primitive::Int(i, signed) => match (i, signed) {
                (Integer::I8, true) => R::I8,
                (Integer::I8, false) => R::U8,
                (Integer::I16, true) => R::I16,
                (Integer::I16, false) => R::U16,
                (Integer::I32, true) => R::I32,
                (Integer::I32, false) => R::U32,
                (Integer::I64, true) => R::I64,
                (Integer::I64, false) => R::U64,
                (Integer::I128, _) => return None,
            },
            Primitive::Pointer(_) => R::U64,
            Primitive::Float(_) => return None,
        })
    };
    let Variants::Multiple { tag, tag_encoding, tag_field, variants: vlayouts } =
        l.layout.variants()
    else {
        return None;
    };
    // Bounds-check BEFORE `FieldsShape::offset`, which panics (rustc_abi
    // lib.rs `offsets[FieldIdx::new(i)]`) rather than returning an Option: a
    // tag_field outside the enum's own FieldsShape must DECLINE the
    // descriptor, never abort the compile (producer totality — lowering fails
    // closed to tags, never to an ICE).
    if tag_field.as_usize() >= l.layout.fields().count() {
        return None;
    }
    let lane_offset = l.layout.fields().offset(tag_field.as_usize()).bytes();
    let lane_ty = repr_of_scalar(*tag)?;
    let encoding = match tag_encoding {
        TagEncoding::Direct => {
            if def.canonical_tag_repr() != Some(lane_ty) {
                return None;
            }
            trust_ir::EnumTagEncoding::Direct { tag_offset: lane_offset }
        }
        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
            trust_ir::EnumTagEncoding::Niche {
                untagged_variant: untagged_variant.as_u32(),
                niche_variants_start: niche_variants.start.as_u32(),
                niche_variants_end: niche_variants.last.as_u32(),
                niche_start: *niche_start,
                niche_offset: lane_offset,
                niche_ty: lane_ty,
            }
        }
    };
    let mut variant_field_offsets = Vec::with_capacity(adt.variants().len());
    for (vidx, variant) in adt.variants().iter_enumerated() {
        let vl = vlayouts.get(vidx)?;
        // `field_offsets` is DECLARATION-indexed (the memory permutation is a
        // separate private field) — read straight through.
        // `.get()`, not `[]`: a variant layout can carry FEWER offsets than
        // the AdtDef variant has fields (uninhabited / degenerate variants),
        // and an IndexVec index would panic. Decline the whole descriptor.
        let offs: Option<Vec<u64>> = (0..variant.fields.len())
            .map(|i| {
                vl.field_offsets.get(rustc_abi::FieldIdx::from_usize(i)).map(|o| o.bytes())
            })
            .collect();
        variant_field_offsets.push(offs?);
    }
    Some(trust_ir::EnumLayoutDescriptor {
        encoding,
        size: l.size.bytes(),
        align: l.align.abi.bytes(),
        variant_field_offsets,
    })
}

/// `needs_drop`, fail-CLOSED on an unrevealed opaque (it MAY need drop).
pub(crate) fn cycle_safe_needs_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    te: ty::TypingEnv<'tcx>,
    ty: RustcTy<'tcx>,
) -> bool {
    !layout_query_is_reentrant_safe(ty) || ty.needs_drop(tcx, te)
}

/// Fallible normalize, skipped for an unrevealed opaque (returned unchanged —
/// both differential sides render the SAME unrevealed alias, so equality
/// comparisons stay meaningful; a mismatch fails closed exactly as before).
pub(crate) fn cycle_safe_normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    te: ty::TypingEnv<'tcx>,
    t: RustcTy<'tcx>,
) -> RustcTy<'tcx> {
    if t.has_non_region_param()
        || t.has_non_region_infer()
        || t.has_non_region_placeholders()
        || t.has_opaque_types()
        || t.has_escaping_bound_vars()
    {
        t
    } else {
        tcx.try_normalize_erasing_regions(te, ty::Unnormalized::new_wip(t)).unwrap_or(t)
    }
}

/// `type_is_copy_modulo_regions`, fail-closed (NOT Copy → callers emit `Move`,
/// matching what built MIR does for a non-Copy place) on an unrevealed opaque.
pub(crate) fn cycle_safe_is_copy<'tcx>(
    tcx: TyCtxt<'tcx>,
    te: ty::TypingEnv<'tcx>,
    ty: RustcTy<'tcx>,
) -> bool {
    layout_query_is_reentrant_safe(ty) && tcx.type_is_copy_modulo_regions(te, ty)
}

/// Trust: true iff `ty` is an interpretable SCALAR (bool or a fixed-width int). A memory-promoted
/// local's slot `Load`/`Store` round-trips a scalar through memory, so only scalar locals are
/// promotable; a non-scalar `&mut` local fails closed at its `let`/param site. Notably this EXCLUDES
/// `Ty::Ptr`, so we never promote a slot whose value is itself a pointer (a `&mut &T`).
fn is_scalar_ty(ty: &Ty) -> bool {
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

/// Trust: does this (producer-emitted) type contain a `Ty::Func` anywhere? Used to refuse
/// HIGHER-ORDER fn-pointer signatures (`map_fn_ptr_ty`) so crate-level splice remapping of
/// `FuncTyId`s never needs to recurse into a signature's own params. The producer's `map_ty`
/// only emits scalars / `Tuple` / `Unit` / `Ptr` / fat-ptr tuples / `Func`, so `Tuple`
/// recursion is exhaustive for everything reachable here; unknown variants conservatively
/// report `true` (fail-closed at the caller).
fn ty_contains_func(ty: &Ty) -> bool {
    match ty {
        Ty::Func(_) => true,
        Ty::Tuple(elems) => elems.iter().any(ty_contains_func),
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
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never => false,
        _ => true,
    }
}

/// Trust: PRECISE fail-closed tag for a `match` scrutinee type the integer-`Switch` path cannot
/// lower (the wave-6 residue split of the old catch-all "Match(non-integer scrutinee)"). A REF
/// scrutinee reports its POINTEE's class — the deref-match path already peeled int/char pointees
/// off before asking, so a ref here has an unmodeled pointee. Deliberate honesty notes:
///   * FLOAT (direct or `&f32`/`&f64`) — "Match(float scrutinee)". Float pattern equality is a
///     SEMANTICS decision (NaN never matches itself, `-0.0` matches `0.0` under IEEE `==` but they
///     differ bitwise); it stays fail-closed and is NEVER lowered silently as int/bit equality.
///   * str/slice/array — byte-string / string-literal / slice patterns are unmodeled shapes
///     (census 2026-07-02: the `&[_]`-cast + byte-literal class dominates the residue).
///   * `Param`/`Alias` — generic or opaque scrutinees (the `for`-loop iterator and `.await`
///     desugar matches land here); no monomorphic layout to switch on.
/// Everything else keeps the original catch-all tag.
fn non_integer_scrut_tag(rty: RustcTy<'_>) -> &'static str {
    let (base, is_ref) = match rty.kind() {
        ty::Ref(_, pointee, _) => (*pointee, true),
        _ => (rty, false),
    };
    match base.kind() {
        ty::Float(_) => "Match(float scrutinee)",
        ty::Str => "Match(str scrutinee)",
        ty::Slice(_) => "Match(slice scrutinee)",
        ty::Array(..) => "Match(array scrutinee)",
        ty::RawPtr(..) => "Match(raw-ptr scrutinee)",
        ty::Param(_) | ty::Alias(..) => "Match(generic/opaque scrutinee)",
        ty::Adt(adt, _) if adt.is_union() => "Match(union scrutinee)",
        _ if is_ref => "Match(ref scrutinee)",
        _ => "Match(non-integer scrutinee)",
    }
}

/// Extract a bare integer-literal value from a constant pattern `value`, in the scrutinee's integer
/// type, as its raw fixed-width bits. Returns `None` (fail-closed) for any
/// constant that is not an integer/char of the scrutinee's type (bool/float/str/aggregate), so
/// non-integer-literal patterns route to `unsupported`. Char patterns retain `Ty::Char` and use
/// their unsigned 32-bit code points as switch-case bits.
///
/// Keeping raw bits until emission preserves the full u128 domain; the caller
/// uses [`integer_constant_from_bits`] to choose the v24-canonical `Int` or
/// `U128` spelling for the scrutinee type.
fn const_pat_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ty::Value<'tcx>,
    _signed: bool,
    _bits: u32,
) -> Option<u128> {
    // Integer-typed constants, plus first-class `char` (an unsigned 32-bit code-point carrier;
    // typeck guarantees a char pattern only ever meets a char scrutinee, whose caller passes
    // `signed = false`, `bits = 32`). Bool/float patterns are
    // out of scope here (bool matches route to `lower_bool_match`).
    if !matches!(value.ty.kind(), ty::Int(_) | ty::Uint(_) | ty::Char) {
        return None;
    }
    let raw: u128 = value.try_to_bits(tcx, ty::TypingEnv::fully_monomorphized())?;
    Some(raw)
}

/// Trust: extract a RANGE pattern's `(lo, hi, included)` as raw fixed-width bounds in the scrutinee's integer
/// type, or `None` (fail-closed) for any range the integer-`Switch`/`ICmp` machinery cannot bound:
///   * a non-integer range type (char/float — the boundary valtree is not an integer leaf), or a
///     range type that disagrees with the scrutinee's integer type;
///   * an OPEN-ended boundary (`..=5`, `1..`, `..` — `NegInfinity`/`PosInfinity`), which would need an
///     unbounded comparison this footing does not model.
/// The caller canonicalizes the bounds exactly like `const_pat_int`, so the emitted
/// `ICmp`s compare in the same constant domain as the literal-`Switch` cases. `included`
/// is `true` for `..=` (`RangeEnd::Included`), `false` for `..` (`RangeEnd::Excluded`); it selects the
/// upper-bound comparison (`x <= hi` vs `x < hi`).
fn range_pat_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    pr: &rustc_middle::thir::PatRange<'tcx>,
    _signed: bool,
    _bits: u32,
) -> Option<(u128, u128, bool)> {
    use rustc_middle::thir::PatRangeBoundary;
    // The range type must be the integer scrutinee's type. A char/float range (or a range whose ty
    // somehow disagrees with the scrutinee) is out of scope for the integer `ICmp` footing.
    if !matches!(pr.ty.kind(), ty::Int(_) | ty::Uint(_)) {
        return None;
    }
    // Both boundaries must be FINITE — an open-ended range (`1..`, `..=5`) is not bounded here.
    let lo_vt = match pr.lo {
        PatRangeBoundary::Finite(vt) => vt,
        PatRangeBoundary::NegInfinity | PatRangeBoundary::PosInfinity => return None,
    };
    let hi_vt = match pr.hi {
        PatRangeBoundary::Finite(vt) => vt,
        PatRangeBoundary::NegInfinity | PatRangeBoundary::PosInfinity => return None,
    };
    // The boundary valtrees are scalar integer leaves of `pr.ty`; read their raw bits and reinterpret
    // in the scrutinee's width/signedness (matching `const_pat_int`'s `try_to_bits` + `sign_extend`).
    let lo_raw = ty::Value { ty: pr.ty, valtree: lo_vt }
        .try_to_bits(tcx, ty::TypingEnv::fully_monomorphized())?;
    let hi_raw = ty::Value { ty: pr.ty, valtree: hi_vt }
        .try_to_bits(tcx, ty::TypingEnv::fully_monomorphized())?;
    let included = matches!(pr.end, rustc_hir::RangeEnd::Included);
    Some((lo_raw, hi_raw, included))
}

/// Bit width of a mapped integer `trust_ir::Ty` (callers have already excluded non-integers).
fn scrut_ty_bits(t: &Ty) -> u32 {
    match t {
        // Trust (v25 B1): faithful scalar switch scrutinees.
        Ty::Isize | Ty::Usize => 64,
        Ty::Char => 32,
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        Ty::I32 | Ty::U32 => 32,
        Ty::I64 | Ty::U64 => 64,
        Ty::I128 | Ty::U128 => 128,
        _ => 128,
    }
}

/// Build the canonical Trust-IR v24 spelling for a fixed-width integer bit
/// pattern. Signed values are sign-extended into `Constant::Int`; unsigned
/// values route through `Constant::u128`, which uses `Int` through
/// `i128::MAX` and `U128` above it. Keeping this constructor centralized
/// prevents the old upper-half-u128-as-negative-Int spelling from reappearing.
pub(crate) fn integer_constant_from_bits(raw: u128, signed: bool, bits: u32) -> Constant {
    if signed { Constant::Int(sign_extend(raw, true, bits)) } else { Constant::u128(raw) }
}

/// Integer literal spelling differs from evaluated raw bits only for a
/// leading unary minus: the literal carries the positive magnitude, including
/// `2^127` for `i128::MIN`. `wrapping_neg` produces that one representable
/// boundary without a debug-build overflow; type checking has already rejected
/// every out-of-range or negative-unsigned literal.
fn integer_literal_constant(raw: u128, neg: bool, signed: bool, bits: u32) -> Constant {
    if neg {
        Constant::Int((raw as i128).wrapping_neg())
    } else {
        integer_constant_from_bits(raw, signed, bits)
    }
}

/// Reinterpret an unsigned `bits`-wide bit pattern `raw` as the `i128` value
/// of a signed integer of that width. Unsigned construction must use
/// `integer_constant_from_bits` so upper-half u128 stays value-faithful.
fn sign_extend(raw: u128, signed: bool, bits: u32) -> i128 {
    if signed && bits < 128 {
        let shift = 128 - bits;
        // Left-then-arithmetic-right shift sign-extends the top set bit of the `bits`-wide value.
        (((raw << shift) as i128) >> shift)
    } else {
        raw as i128
    }
}

/// Extract the bound `LocalVarId` from a simple binding pattern (`let x = …`).
/// THIR has already resolved type ascriptions, so a plain `Binding` is all we look for.
/// Compound patterns (tuple/struct destructuring) are not bound yet → `None`.
fn binding_var(pat: &Pat<'_>) -> Option<LocalVarId> {
    match &pat.kind {
        PatKind::Binding { var, .. } => Some(*var),
        _ => None,
    }
}

/// Trust (C2-names): the binding's source-level NAME, the sibling of [`binding_var`].
fn binding_name(pat: &Pat<'_>) -> Option<rustc_span::Symbol> {
    match &pat.kind {
        PatKind::Binding { name, .. } => Some(*name),
        _ => None,
    }
}

/// Trust (wave-LD): an owned, `self.thir`-independent plan for binding an IRREFUTABLE `let`-destructure
/// pattern (`let (a, b) = t;`, `let [x, y, z] = arr;`, `let Point { x, y } = p;`, nested combinations).
/// `binding_var` returns `Some` only for a bare `PatKind::Binding` (`let x = …`); every compound pattern
/// returns `None`, so before this wave `let (a, b) = t;` lowered `t` for effects but bound NEITHER `a`
/// NOR `b` — each later use fell closed at `VarRef(unbound)`. `build_bind_node` snapshots the pattern
/// TREE into this owned form (reading `self.thir` only, borrowing nothing across the later mutating
/// emit), and `Lowerer::emit_bind` walks it against the init value, emitting one logical `ExtractField`
/// per traversed aggregate field (declaration/position index — the SAME convention the tuple/struct/array
/// MATCH path uses) and `set_local` at each leaf. No byte offsets: `ExtractField` is a LOGICAL field
/// access the interpreter/comparator resolve identically on both sides, so a reordered struct is correct
/// by construction (unlike the by-REF enum-payload GEP path, which needs a memory offset).
enum BindNode {
    /// `_` wildcard — bind nothing under this position.
    Skip,
    /// A by-value binding `x` (optionally with an `x @ subpat` inner destructure at the SAME value).
    Bind(LocalVarId, Option<Box<BindNode>>),
    /// A tuple/struct/array destructure: for each `(field-or-element index, subplan)`.
    Fields(Vec<(u32, BindNode)>),
}

/// Trust (wave-LD): build the owned binding plan for an irrefutable `let` pattern, or `None` for any
/// shape not modeled (fail-closed → caller keeps the pre-wave behaviour: lower the init, bind nothing).
/// Reads the pattern only; mints no IR and touches no `Lowerer` state.
fn build_bind_node(pat: &Pat<'_>) -> Option<BindNode> {
    match &pat.kind {
        PatKind::Wild => Some(BindNode::Skip),
        // A by-VALUE binding. `ref x` / `ref mut x` (`ByRef::Yes`) needs an interior reference (a GEP,
        // like the enum by-ref payload path) — out of scope here, fail closed.
        PatKind::Binding {
            var,
            mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
            subpattern,
            ..
        } => {
            let inner = match subpattern {
                Some(sp) => Some(Box::new(build_bind_node(sp)?)),
                None => None,
            };
            Some(BindNode::Bind(*var, inner))
        }
        // Tuple / struct destructure — `sp.field` is the declaration index (== the `ExtractField` field
        // index the struct/tuple MATCH path already uses).
        PatKind::Leaf { subpatterns } => {
            let mut fields = Vec::new();
            for sp in subpatterns.iter() {
                fields.push((sp.field.as_u32(), build_bind_node(&sp.pattern)?));
            }
            Some(BindNode::Fields(fields))
        }
        // Fixed-length array destructure WITHOUT a `..` rest (`[a, b, c]`). `map_ty` lowers `[T; N]`
        // (N>0) to `Ty::Tuple`, so the element read is `ExtractField` at the positional index — exactly
        // the tuple case. A REST pattern (`slice: Some`) binds a fat subslice → not modeled (fail closed).
        PatKind::Array { prefix, slice: None, suffix } => {
            let mut fields = Vec::new();
            for (i, p) in prefix.iter().chain(suffix.iter()).enumerate() {
                fields.push((i as u32, build_bind_node(p)?));
            }
            Some(BindNode::Fields(fields))
        }
        // Everything else — `ref` binding, or-pattern, array-with-rest, slice, deref/box, constant,
        // range, enum-variant (refutable — a `let-else`), etc. — is not an irrefutable by-value
        // destructure we model. Fail closed.
        _ => None,
    }
}

/// Trust (wave-LD): does this plan bind at least one local? An all-`Skip` subtree (`let (_, _) = t;`)
/// binds nothing, so its `ExtractField` reads are dead — skip emitting them.
fn bind_node_binds(node: &BindNode) -> bool {
    match node {
        BindNode::Skip => false,
        BindNode::Bind(..) => true,
        BindNode::Fields(fields) => fields.iter().any(|(_, n)| bind_node_binds(n)),
    }
}

/// Trust (wave-TD, 2026-07-14): a plain TUPLE destructure pattern — one
/// `Option<LocalVarId>` slot per tuple position (`Some(var)` for a plain by-value
/// binding, `None` for `_`/an elided position) when the pattern is
/// `PatKind::Leaf` over a `ty::Tuple` and EVERY subpattern is a wildcard or a
/// plain by-value binding. Anything else — a single-variant ADT `Leaf`
/// (`Foo { a }` — filtered by the `ty::Tuple` check), a by-ref/nested/or
/// subpattern — returns `None`, and `lower_stmt` keeps the pre-wave fallthrough
/// verbatim (the init lowers for effects, the bindings stay unbound, every use
/// fails closed at its own site).
fn tuple_pat_bindings(pat: &Pat<'_>) -> Option<Vec<Option<LocalVarId>>> {
    let PatKind::Leaf { subpatterns } = &pat.kind else { return None };
    let ty::Tuple(comps) = pat.ty.kind() else { return None };
    let mut out: Vec<Option<LocalVarId>> = vec![None; comps.len()];
    for sp in subpatterns {
        let slot = out.get_mut(sp.field.as_usize())?;
        match &sp.pattern.kind {
            PatKind::Wild => {}
            PatKind::Binding {
                var,
                mode: rustc_hir::BindingMode(rustc_hir::ByRef::No, _),
                subpattern: None,
                ..
            } => *slot = Some(*var),
            _ => return None,
        }
    }
    Some(out)
}

/// Trust: a control-flow arm's open (not-yet-terminated) block, snapshotted so its branch terminator
/// can be appended LATER — once the cross-arm merged-local set (and hence the `Br` arg list) is known.
struct OpenBlock {
    id: BlockId,
    params: Vec<(ValueId, Ty)>,
    body: Vec<InstrNode>,
}

/// Trust: the captured outcome of lowering one `if`/`match` arm body, for the deferred-`Br` SSA-merge.
/// `Reaching` arms flow to the join (and carry their post-arm `locals` so each mutated local's per-arm
/// value can be passed as a join arg); `Diverged` arms (a `return`, or a sealed `Unreachable`
/// value-hole) do not.
enum CapturedArm {
    Reaching {
        open: OpenBlock,
        /// The arm's binding environment AFTER lowering its body (post-arm local versions).
        locals: Vec<(LocalVarId, ValueId)>,
        /// The arm's result value (`None` for a unit/non-value-producing arm).
        result: Option<ValueId>,
    },
    Diverged,
}

impl CapturedArm {
    /// A no-body fall-through arm (the implicit `else` of an else-less `if`): reaches the join with no
    /// result, carrying the supplied (pre-split) local versions.
    fn reaching(open: OpenBlock, locals: Vec<(LocalVarId, ValueId)>) -> Self {
        CapturedArm::Reaching { open, locals, result: None }
    }
    fn is_reaching(&self) -> bool {
        matches!(self, CapturedArm::Reaching { .. })
    }
    /// The arm's post-body `locals` snapshot, or `None` for a diverged arm (no predecessor edge).
    fn locals(&self) -> Option<&[(LocalVarId, ValueId)]> {
        match self {
            CapturedArm::Reaching { locals, .. } => Some(locals),
            CapturedArm::Diverged => None,
        }
    }
}

/// Trust: last-write-wins lookup of `var`'s `ValueId` in a `locals` snapshot (mirrors `local_value`,
/// but over an arbitrary borrowed slice so it works on captured arm snapshots).
fn last_value(locals: &[(LocalVarId, ValueId)], var: LocalVarId) -> Option<ValueId> {
    locals.iter().rev().find(|(v, _)| *v == var).map(|(_, val)| *val)
}

/// Trust: did `after` change the last-write-wins value of any local that existed in `before`? Used by
/// `lower_match` to fail-closed when a match-arm GUARD reassigns a local (a guard-test block's
/// successors are dispatch edges, not the join, so no block-param merge path exists for it; arm
/// BODIES merge through join params instead). New locals introduced inside the guard/arm (a `let`
/// local-to-the-arm, a pattern binding) are NOT a cross-join reassignment, so only pre-existing
/// locals are checked.
fn locals_changed(before: &[(LocalVarId, ValueId)], after: &[(LocalVarId, ValueId)]) -> bool {
    let mut seen: Vec<LocalVarId> = Vec::new();
    for (var, _) in before {
        if seen.contains(var) {
            continue;
        }
        seen.push(*var);
        if last_value(before, *var) != last_value(after, *var) {
            return true;
        }
    }
    false
}

/// Map rustc MIR `BinOp` → trust_ir `BinOp` (arithmetic/bitwise subset; extend as coverage grows).
/// Comparison ops never reach here — they route to `map_icmp` → `Inst::ICmp` in `lower_expr`.
/// Trust: `signed` selects the signedness-correct division/remainder/right-shift form
/// (`SDiv`/`UDiv`, `SRem`/`URem`, `AShr`/`LShr`), mirroring trust-ir-bridge's `map_binop`
/// (crates/trust-ir-bridge/src/lower.rs:282-291); the old sign-oblivious `Div → SDiv` mis-lowered
/// unsigned division.
fn map_binop(op: MirBinOp, signed: bool) -> BinOp {
    match op {
        MirBinOp::Add | MirBinOp::AddUnchecked | MirBinOp::AddWithOverflow => BinOp::Add,
        MirBinOp::Sub | MirBinOp::SubUnchecked | MirBinOp::SubWithOverflow => BinOp::Sub,
        MirBinOp::Mul | MirBinOp::MulUnchecked | MirBinOp::MulWithOverflow => BinOp::Mul,
        MirBinOp::Div => {
            if signed {
                BinOp::SDiv
            } else {
                BinOp::UDiv
            }
        }
        MirBinOp::Rem => {
            if signed {
                BinOp::SRem
            } else {
                BinOp::URem
            }
        }
        MirBinOp::BitAnd => BinOp::And,
        MirBinOp::BitOr => BinOp::Or,
        MirBinOp::BitXor => BinOp::Xor,
        MirBinOp::Shl | MirBinOp::ShlUnchecked => BinOp::Shl,
        MirBinOp::Shr | MirBinOp::ShrUnchecked => {
            if signed {
                BinOp::AShr
            } else {
                BinOp::LShr
            }
        }
        // Non-comparison op not yet distinguished; conservative placeholder (extend as needed).
        _ => BinOp::Add,
    }
}

/// Map the integer-arithmetic `mir::BinOp`s that have a checked (overflowing) form to the
/// corresponding `trust_ir::OverflowOp`. Only `+`/`-`/`*` get a `(result, overflowed)` pair plus an
/// overflow `Assert` (matching rustc's `AddWithOverflow`/`AssertKind::Overflow` MIR shape); every
/// other op (div/rem/bitwise/shift) returns `None` and lowers to a plain wrapping `BinOp`.
fn map_overflow_op(op: MirBinOp) -> Option<OverflowOp> {
    match op {
        MirBinOp::Add => Some(OverflowOp::AddOverflow),
        MirBinOp::Sub => Some(OverflowOp::SubOverflow),
        MirBinOp::Mul => Some(OverflowOp::MulOverflow),
        _ => None,
    }
}

/// Map a comparison `mir::BinOp` on FLOAT operands → `trust_ir::FCmpOp`. Byte-for-byte the
/// MIR-side oracle's table (trust-ir-bridge `map_float_binop`, lower.rs:362-367): the ORDERED
/// forms for `==`/`<`/`<=`/`>`/`>=` (false when either operand is NaN) and the UNORDERED form
/// for `!=` (true when either operand is NaN) — exactly Rust's IEEE-754 semantics, where
/// `NaN != x` is the single NaN-true comparison. Returns `None` for non-comparison ops (the
/// caller routes those to the float-arithmetic emitter).
fn map_fcmp(op: MirBinOp) -> Option<FCmpOp> {
    Some(match op {
        MirBinOp::Eq => FCmpOp::OEq,
        MirBinOp::Ne => FCmpOp::UNe,
        MirBinOp::Lt => FCmpOp::OLt,
        MirBinOp::Le => FCmpOp::OLe,
        MirBinOp::Gt => FCmpOp::OGt,
        MirBinOp::Ge => FCmpOp::OGe,
        _ => return None,
    })
}

/// Map a comparison `mir::BinOp` → `trust_ir::ICmpOp` (signed selects `S*`, unsigned `U*`).
/// Returns `None` for non-comparison ops (the caller emits a `BinOp` instead).
fn map_icmp(op: MirBinOp, signed: bool) -> Option<ICmpOp> {
    Some(match op {
        MirBinOp::Eq => ICmpOp::Eq,
        MirBinOp::Ne => ICmpOp::Ne,
        MirBinOp::Lt => {
            if signed {
                ICmpOp::Slt
            } else {
                ICmpOp::Ult
            }
        }
        MirBinOp::Le => {
            if signed {
                ICmpOp::Sle
            } else {
                ICmpOp::Ule
            }
        }
        MirBinOp::Gt => {
            if signed {
                ICmpOp::Sgt
            } else {
                ICmpOp::Ugt
            }
        }
        MirBinOp::Ge => {
            if signed {
                ICmpOp::Sge
            } else {
                ICmpOp::Uge
            }
        }
        _ => return None,
    })
}

fn variant_name(kind: &ExprKind<'_>) -> &'static str {
    match kind {
        ExprKind::Deref { .. } => "Deref",
        ExprKind::Unary { .. } => "Unary",
        ExprKind::Cast { .. } => "Cast",
        ExprKind::Loop { .. } => "Loop",
        ExprKind::Match { .. } => "Match",
        ExprKind::Assign { .. } => "Assign",
        ExprKind::Field { .. } => "Field",
        ExprKind::Index { .. } => "Index",
        ExprKind::Borrow { .. } => "Borrow",
        ExprKind::Tuple { .. } => "Tuple",
        ExprKind::Adt { .. } => "Adt",
        // Trust: wave-5 — closure CONSTRUCTION in a VALUE position (call arg, return value,
        // field, reassignment, …). Only the non-capturing literal in a `let` init
        // (`lower_stmt`'s skip) or in `ClosureCall` receiver position is modeled; a
        // first-class closure VALUE needs a `Ty::Closure`/`Constant::Closure` representation
        // the producer does not emit yet. Split from the catch-all "Other" so the ratchet
        // measures the remaining closure-value gap precisely.
        ExprKind::Closure(..) => "Closure(value position)",
        // Trust: a captured-variable read INSIDE a closure body (`ExprKind::UpvarRef` — the
        // capture is a projection off the closure's environment param). Lowering it faithfully
        // needs the env-frame layout model (which field of the capture struct, by-ref vs
        // by-value) that closure construction does not emit yet. Split from the catch-all
        // "Other" so the ratchet measures the capturing-closure-body gap precisely.
        ExprKind::UpvarRef { .. } => "UpvarRef(capturing env)",
        _ => "Other",
    }
}

#[cfg(test)]
mod u128_v24_constant_tests {
    use super::*;

    #[test]
    fn raw_unsigned_128_bits_use_the_canonical_upper_half_variant() {
        assert_eq!(
            integer_constant_from_bits(i128::MAX as u128, false, 128),
            Constant::Int(i128::MAX),
        );
        assert_eq!(
            integer_constant_from_bits(i128::MAX as u128 + 1, false, 128),
            Constant::U128(i128::MAX as u128 + 1),
        );
        assert_eq!(integer_constant_from_bits(u128::MAX, false, 128), Constant::U128(u128::MAX),);
    }

    #[test]
    fn signed_min_literal_does_not_overflow_the_lowerer() {
        assert_eq!(
            integer_literal_constant(1u128 << 127, true, true, 128),
            Constant::Int(i128::MIN),
        );
    }
}
