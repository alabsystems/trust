//! Trust (OD-1 phase 1, ruled 2026-10-03; docs/DECISION_QUEUE.md "OD-1"): INSTANCE
//! HYPOTHESES for open generic dispatch. The design of record is
//! docs/design/2026-10-03-open-generic-dispatch-obligations.md; this module is its
//! phase 1 (in-crate) and phase 2 (a dependency's generics, re-derived here).
//!
//! ## The claim that changes
//!
//! A call `<P as Tr>::m` in a generic body `f`, where `P` mentions only `f`'s own type
//! parameters, `Tr` is open and uncontracted and `Instance::try_resolve` answers
//! `Ok(None)`, used to carry the claim "panic-free for EVERY instantiation" — false by
//! construction (a downstream impl may panic), so its row was published `failed`
//! (DECISION_QUEUE "L0 refutation rows", class (c)). At an ADMITTED site (§2.3,
//! [`admitted_sites`]) the body claims instead `H_f(τ) ⇒ panic-free(f<τ>)`: the
//! call's panic-freedom is a named premise, one `assumption:instance-hypothesis` row
//! PER SITE (outcome `skipped`, solver `trust-classifier`), and the bridge lowers the
//! call with no `Assert(false)` marker and no `PanicFreedom` obligation — so it is no
//! fold site of the whole-function panic-freedom aggregate, and the old one-row-per-
//! body masking is gone — while havocking its result and every place it can write
//! (`trust_ir_bridge::InstanceHypothesisSites`).
//!
//! Lanes (D9's template): advisory counts the rows `assumed`; the strict (default)
//! lane passes CONDITIONALLY (`trust_types::assumption::strict_policy_publishes_
//! assumption_row`); `certify` refuses the function. The rows stay in the
//! denominator, grant no credit and are never `proved`. A body carrying one is never
//! registered panic-free, never a Φ discharge, never `compiler_total`, never a `dyn`
//! reliance premise: `verdict_premise_decline` refuses it in the one authenticator
//! every premise lane consults (`CrateVerificationState::instance_hypothesis_verdicts`).
//!
//! ## Discharge rows and the inventory
//!
//! For each CONCRETE instance `f<τ>` named in a walked body of this crate — a call or
//! any other mention of the fn item (reification) — each admitted site gets one
//! discharge row, keyed by the INTERNED instance (`(DefId, block, args pointer)`), never
//! by a rendered name: the site's callee is substituted and resolved under
//! `TypingEnv::fully_monomorphized()`, and the row carries that callee's own verdict
//! (`proved` when its body discharges panic-freedom on the shared evidence bar,
//! `failed` when it does not and its own ledger carries evidence it can panic, or
//! nothing resolves, `unknown` when its only non-proofs are absent callees,
//! unmodeled MIR and unsafe blocks declared on their `// SAFETY:` comment
//! (`trait_panic_free::refusal_carries_no_violation_evidence`) or its body is
//! outside this crate). Every non-`proved` discharge is an error on
//! the fail-closed lanes ([`report_unestablished_discharges`]). A mention whose arguments are still
//! generic (`g<U>` calling `f::<U>`) PROPAGATES: the enclosing generic gets one
//! `assumption:instance-hypothesis` row per site of `f`, and its own instances
//! discharge `f`'s sites through it (depth-capped). The inventory is never the codegen
//! mono collector's, so every crate with a hypothesis also gets ONE
//! `assumption:instance-hypothesis:inventory-incomplete` row. Nothing is retired on
//! the inventory's strength: definition rows are never removed in phase 1.
//!
//! Trust (OD-1 item 19, 2026-10-06): an instance no body names but a VTABLE or DROP
//! GLUE of a walked body creates (`&W(Bad) as &dyn Run`, `drop(D(Bad))`, also at a
//! still-generic type inside a local generic reached at a named instance) is
//! discharged the same way, off the body's recorded mentioned items ([`glue`]).
//!
//! ## Phase 2: a dependency's generics (OD-1, 2026-10-05)
//!
//! An instance this compilation names of a DEPENDENCY generic (`dep::f::<Bad>`) is
//! discharged exactly as a local carrier's instance is, against sites RE-DERIVED here
//! from the dependency's encoded MIR ([`foreign_carrier_records`]) — D4's channel: the
//! crate must be in the build-declared bundling scope by identity, statically linked
//! and not the sysroot; no rmeta table, no verdict, no policy and no `-Ztrust-verify`
//! setting of the dependency is read, so a verify-off, advisory and strict dependency
//! are charged identically and there is no export to forge or go stale. Every open
//! dispatch of the dependency body is a site, admitted there or not (the superset);
//! still-generic calls into other declared dependency generics propagate. A resolved
//! callee in a re-derivable dependency is judged on the shared bar over a verdict
//! computed HERE (D4-A), so a panicking dependency impl is a `failed` discharge. A
//! local generic calling a dependency carrier at its own parameters publishes the
//! carrier's sites as propagated hypothesis rows, but the call is never lowered under
//! them (the carrier's relative verdict is not re-derived) and keeps its absent-callee
//! row. The dependency's own definition rows are its own and are never retired; an
//! undeclared dependency is unchanged (its calls keep their fail-closed rows).
//!
//! ## Open shapes (OD-1 item 14, 2026-10-04)
//!
//! * A call through a closure type parameter (`<F as Fn<A>>::call` and the `FnMut` /
//!   `FnOnce` twins) is admitted by the same predicate; the indirect-call gate exempts
//!   the dispatched `Self` of an admitted site ([`dispatch_site_blocks`]). Not admitted,
//!   it is class (c) like any other open dispatch.
//! * A call through a fn pointer this body reified from an open trait item at its own
//!   parameters ([`SiteKind::Pointer`]) is the same dispatch and is admitted and
//!   discharged the same way.
//! * A still-generic call to a hypothesis-carrying local body is LOWERED under the
//!   propagated hypotheses when the callee passes the instance-RELATIVE evidence bar
//!   ([`via_call_admits`]); otherwise it keeps its absent-callee row, which is stamped
//!   class (c) when the callee's own row is an open-dispatch refutation that stays open
//!   at the call's arguments (`propagated_open_dispatch_refutation`).
//! * A `dyn` call is never admitted (a vtable has no instance inventory); it is class
//!   (c) when an adversary can supply the impl (`virtual_dispatch_is_adversarial`).
//!
//! ## What is not admitted (keeps class (c), `failed`)
//!
//! A body with any unsafe operation (D33's fence plus own/inlined user `unsafe`),
//! polymorphic recursion, a site with a raw-pointer argument, a site whose arguments
//! let the callee write a place the one-level havoc cannot cover (see [`decide_arg`]),
//! coroutines, async closures, closures whose typeck root is not a plain `fn`, every
//! other non-`fn` body, and every site a user axiom, an ABI/type-total classification
//! or a rung-1/rung-2/D4-B discharge already decided. No trait list.
//!
//! Trust (OD-1 item 20, T6, 2026-10-10): a PLAIN CLOSURE of a plain `fn` is admitted
//! like the `fn` itself ([`is_plain_closure_of_fn`]): a call on a captured callable
//! (`|m| paths(m)` with `paths: impl FnMut`) is the root's own open dispatch, and its
//! instances are discharged where the root's instance walk reaches the closure,
//! whether the root calls it, hands it on, or reifies it into a fn pointer (the glue
//! walk discharges every carrier a walked body mentions, not only those it calls).

use super::{PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{BasicBlock, Body, ConstOperand, Location, TerminatorKind};
use rustc_middle::ty::{self, GenericArgs, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;
use rustc_span::{Span, sym};
use trust_types::assumption::{
    INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX, INSTANCE_HYPOTHESIS_ASSUMPTION_TAG,
    INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND, INSTANCE_HYPOTHESIS_INVENTORY_INCOMPLETE_TAG,
    INSTANCE_HYPOTHESIS_ROW_SOLVER, is_instance_hypothesis_assumption_row,
    is_instance_hypothesis_discharge_row,
};
use trust_types::{Outcome, SourceSpan, TransportObligationResult};

/// Depth cap of the propagation chain (the argument shape walk has its own,
/// [`SHAPE_DEPTH_CAP`], since OD-1 item 18). A propagation chain deeper than this
/// publishes a `failed` discharge row. Same order as the bundle's
/// `NATIVE_TRUST_IR_MAX_INSTANTIATIONS_PER_DEF`, which bounds the same runaway.
const DEPTH_CAP: u32 = 8;

/// Trust (OD-1 item 18, 2026-10-06): depth cap of the ARGUMENT SHAPE WALK alone
/// (the propagation chain keeps [`DEPTH_CAP`]). At 8 the walk ran out inside every
/// `String` held one ADT deeper than a direct argument: serde-derive's by-value
/// `__Visitor { marker: PhantomData<Rec> }` reaches `Rec -> String -> Vec -> RawVec ->
/// RawVecInner -> Unique<u8> -> u8` at depth 9, which the walk answered `Opaque`
/// (refused: "a by-value argument that holds a raw pointer or an opaque part"). The
/// walk is exact up to the cap and every type beyond it is still `Opaque` (refused);
/// recursion is caught by the type stack, not by the cap. A precision change only.
///
/// Trust (OD-1 item 18 follow-up T3, 2026-10-10): raised 16 -> 64. Since the item 18
/// review the walk's COST is bounded by [`SHAPE_NODE_BUDGET`] alone, so this cap only
/// bounds the walk's recursion (stack) depth; at 16 it still refused, as "opaque",
/// owned nesting the budget walks with room to spare. Every `Vec`/`String` layer
/// costs three or four levels (`Vec -> RawVec -> PhantomData<T> -> T`), so a serde
/// argument over records of records reached the cap with no pointer anywhere:
/// preview3's tla-cert `&Vec<CertificateStep>` (`CertificateStep -> Justification ->
/// Vec<CaseBranch> -> Vec<(StepId, Formula)> -> Formula -> Vec<Term> -> String`, about
/// 20 levels, a few hundred nodes) and the by-value `__Visitor { marker:
/// PhantomData<Certificate> }` of every `deserialize_struct`. A type deeper than 64
/// or larger than the budget is still `Opaque` (refused), so the change only admits
/// shapes the walk now sees through EXACTLY, decided by the unchanged [`decide_arg`].
const SHAPE_DEPTH_CAP: u32 = 64;

/// Trust (OD-1 item 18 review fix, 2026-10-06): NODE BUDGET of one argument shape
/// walk ([`shape_of`]). [`shape_rec`] re-walks every field occurrence of a type (the
/// [`Shape`] it builds is a tree, not a DAG), so its cost is about
/// `branching ^ depth`: with the cap raised to 16, a chain of plain structs each
/// holding four copies of the next took 31 s at 15 levels and eight copies at 12
/// levels did not finish in 180 s, once per argument of every candidate site. Every
/// visit spends one unit; once the budget is spent every further visit answers
/// [`Shape::Opaque`], which [`decide_arg`] refuses whatever the access path — so
/// exhausting it only ever refuses more (fail-closed). The largest argument in the
/// two measured crates (serde-derive visitors over `String`/`Vec` records) walks a few
/// hundred nodes; 4096 leaves an order of magnitude of headroom and bounds the walk.
const SHAPE_NODE_BUDGET: u32 = 4096;

// ---------------------------------------------------------------------------
// The argument predicate (pure core, unit-tested).
// ---------------------------------------------------------------------------

/// What an argument hands the callee, as far as the generic body's model is
/// concerned. Built from the rustc type by [`shape_of`]; decided by [`decide_arg`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Shape {
    /// A scalar, a fn item or fn pointer: nothing the callee can write.
    Plain,
    /// `str`: plain bytes, unsized.
    Str,
    /// A type parameter or an associated-type projection of one. The generic body's
    /// model carries no value for it (the extractor has no type to give it), so no
    /// fact about it can go stale.
    Generic,
    Ref {
        mutable: bool,
        pointee: Box<Shape>,
    },
    /// An OWNING pointer (`Box`, `core::ptr::Unique` — so `Vec`/`String` contents).
    Owned(Box<Shape>),
    /// A raw pointer or `NonNull`: may alias anything, including the caller's locals.
    RawPtr,
    UnsafeCell(Box<Shape>),
    /// Fields of an aggregate (struct/enum/union, tuple, array, closure captures,
    /// and the type argument of `PhantomData`, read as owned).
    Fields(Vec<Shape>),
    /// `[T]`: unsized.
    Slice(Box<Shape>),
    /// Anything the walk cannot see through: `dyn`, coroutines, foreign types, opaque
    /// `impl Trait`, recursion across a reference or a cell, depth beyond
    /// [`SHAPE_DEPTH_CAP`].
    Opaque,
}

/// The decision for one argument of a candidate site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ArgDecision {
    /// The callee can write nothing the body's model holds a value for.
    Inert,
    /// The callee may write the argument's pointee, and nothing else the model holds:
    /// the bridge stores a fresh value through it.
    Havoc,
    /// The callee may write a place the one-level havoc cannot cover (or one nobody
    /// can see): the site is not admitted.
    Refuse(&'static str),
}

#[derive(Default)]
struct Reach {
    /// A `&mut` reached while the memory is writable.
    mut_ref: bool,
    /// Any other reference reached.
    shared_ref: bool,
    raw_ptr: bool,
    owned_ptr: bool,
    /// An `UnsafeCell` reached only through shared access (the callee may write it,
    /// and the caller may still observe it).
    interior_shared: bool,
    opaque: bool,
}

fn reach(shape: &Shape, shared: bool, out: &mut Reach) {
    match shape {
        Shape::Plain | Shape::Str | Shape::Generic => {}
        Shape::Ref { mutable, pointee } => {
            if *mutable && !shared {
                out.mut_ref = true;
            } else {
                out.shared_ref = true;
            }
            reach(pointee, shared || !*mutable, out);
        }
        Shape::Owned(pointee) => {
            out.owned_ptr = true;
            reach(pointee, shared, out);
        }
        Shape::RawPtr => out.raw_ptr = true,
        Shape::UnsafeCell(inner) => {
            if shared {
                out.interior_shared = true;
            }
            // The cell's contents are writable whatever the access path.
            reach(inner, false, out);
        }
        Shape::Fields(fields) => fields.iter().for_each(|field| reach(field, shared, out)),
        Shape::Slice(element) => reach(element, shared, out),
        Shape::Opaque => out.opaque = true,
    }
}

fn is_unsized(shape: &Shape) -> bool {
    matches!(shape, Shape::Str | Shape::Slice(_) | Shape::Opaque)
}

/// Can the callee, handed this argument, write a place the generic body's model
/// holds a value for, and can the bridge's one-level havoc cover it?
///
/// * a raw pointer: refused (design §2.3);
/// * `&mut P`: the pointee is havocked, so `P` must hold no reference or pointer of
///   its own (a write through it would not be covered) and must be sized;
/// * `&P`: inert unless `P` holds interior mutability reachable through the shared
///   access, in which case it is havocked under the same conditions as `&mut P`;
///   a raw pointer or an opaque part inside `P` is refused (it may alias anything);
/// * by value: the value moves into the callee, so only what it BORROWS matters: a
///   `&mut`, a raw pointer, an opaque part, or a shared reference to interior
///   mutability is refused; owned contents (`Box`, `Vec`) are not observable after.
pub(super) fn decide_arg(arg: &Shape) -> ArgDecision {
    match arg {
        Shape::RawPtr => ArgDecision::Refuse("a raw-pointer argument"),
        Shape::Ref { mutable: true, pointee } => {
            if is_unsized(pointee) {
                return ArgDecision::Refuse("a `&mut` to an unsized or opaque pointee");
            }
            let mut r = Reach::default();
            reach(pointee, false, &mut r);
            if r.mut_ref || r.shared_ref || r.raw_ptr || r.owned_ptr || r.opaque {
                return ArgDecision::Refuse(
                    "a `&mut` whose pointee holds a reference or pointer the havoc cannot cover",
                );
            }
            ArgDecision::Havoc
        }
        Shape::Ref { mutable: false, pointee } => {
            let mut r = Reach::default();
            reach(pointee, true, &mut r);
            if r.raw_ptr || r.opaque {
                return ArgDecision::Refuse(
                    "a `&` whose pointee holds a raw pointer or an opaque part",
                );
            }
            if !r.interior_shared {
                return ArgDecision::Inert;
            }
            if is_unsized(pointee) || r.mut_ref || r.shared_ref || r.owned_ptr {
                return ArgDecision::Refuse(
                    "interior mutability behind a reference or pointer the havoc cannot cover",
                );
            }
            ArgDecision::Havoc
        }
        by_value => {
            let mut r = Reach::default();
            reach(by_value, false, &mut r);
            if r.mut_ref {
                ArgDecision::Refuse("a by-value argument that holds a `&mut`")
            } else if r.raw_ptr || r.opaque {
                ArgDecision::Refuse(
                    "a by-value argument that holds a raw pointer or an opaque part",
                )
            } else if r.interior_shared {
                ArgDecision::Refuse(
                    "a by-value argument that holds a shared reference to interior mutability",
                )
            } else {
                ArgDecision::Inert
            }
        }
    }
}

/// Why a body admits no site at all (design §2.3's body conjuncts).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BodyRefusal {
    NotAFunction,
    UnsafeOperation,
    PolymorphicRecursion,
}

/// The body conjuncts of the admission predicate, pure.
pub(super) fn body_admits(
    is_plain_fn: bool,
    unsafe_operation: bool,
    polymorphic_recursion: bool,
) -> Result<(), BodyRefusal> {
    if !is_plain_fn {
        Err(BodyRefusal::NotAFunction)
    } else if unsafe_operation {
        Err(BodyRefusal::UnsafeOperation)
    } else if polymorphic_recursion {
        Err(BodyRefusal::PolymorphicRecursion)
    } else {
        Ok(())
    }
}

/// The site conjuncts, pure: the call is an unresolved (`Ok(None)`) trait-method
/// dispatch whose generic arguments mention only the body's own parameters, no other
/// classification decided it, and every argument is admissible. `Ok` carries the
/// argument indices the bridge havocs.
pub(super) fn site_admits(
    unresolved_trait_dispatch: bool,
    own_params_only: bool,
    decided_elsewhere: bool,
    args: &[ArgDecision],
) -> Result<Vec<usize>, &'static str> {
    if !unresolved_trait_dispatch {
        return Err("not an unresolved trait-method dispatch");
    }
    if decided_elsewhere {
        return Err("already classified (user axiom, ABI/type total, rung 1/2, D4-B)");
    }
    if !own_params_only {
        return Err("a generic argument mentions something other than the body's own parameters");
    }
    let mut havoc = Vec::new();
    for (index, decision) in args.iter().enumerate() {
        match decision {
            ArgDecision::Inert => {}
            ArgDecision::Havoc => havoc.push(index),
            ArgDecision::Refuse(reason) => return Err(reason),
        }
    }
    Ok(havoc)
}

// ---------------------------------------------------------------------------
// rustc -> Shape.
// ---------------------------------------------------------------------------

fn is_core_unique(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.crate_name(did.krate) == sym::core && tcx.item_name(did).as_str() == "Unique"
}

/// Trust (1.101): `alloc`'s `RawVecInner` — the type-erased allocation owner
/// inside every `RawVec` (so every `Vec`/`String`). In 1.99 its pointer field
/// was `Unique<u8>`, which the walk shapes as OWNING; 1.101 spells it
/// `NonNull<u8>`, which the walk would shape as a raw pointer and refuse every
/// `Vec` contents argument. The ownership fact did not move: `RawVecInner`
/// is `pub(crate)` to `alloc`, is constructed only by `RawVec`, and uniquely
/// owns its allocation exactly as the `Unique` did; the element shape still
/// arrives through `RawVec`'s `PhantomData<T>` field, so the erased bytes
/// shape as an owned plain buffer.
fn is_alloc_raw_vec_inner(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.crate_name(did.krate) == sym::alloc && tcx.item_name(did).as_str() == "RawVecInner"
}

/// The shape of an argument of type `ty` in a body whose typing environment is
/// `typing_env`. Every type is NORMALIZED in that environment before it is shaped
/// (the argument's own type and every ADT field type, which `FieldDef::ty` hands
/// back unnormalized): a projection that normalizes to a raw pointer, a `&mut` or a
/// shared reference to interior mutability is shaped as what it IS, never as an
/// inert [`Shape::Generic`]. A type that does not normalize is [`Shape::Opaque`].
pub(super) fn shape_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Shape {
    let mut walk =
        ShapeWalk { stack: Vec::new(), budget: SHAPE_NODE_BUDGET, depth_exhausted: false };
    let shape = match normalized(tcx, typing_env, ty::Unnormalized::new_wip(ty)) {
        Some(ty) => shape_rec(tcx, typing_env, ty, SHAPE_DEPTH_CAP, false, &mut walk),
        None => Shape::Opaque,
    };
    if super::env_flag_enabled("TRUST_INSTANCE_HYPOTHESIS_DEBUG") {
        if walk.budget == 0 {
            eprintln!(
                "[INSTANCE_HYPOTHESIS] shape walk of `{ty}` spent its {SHAPE_NODE_BUDGET}-node budget: opaque"
            );
        }
        if walk.depth_exhausted {
            eprintln!(
                "[INSTANCE_HYPOTHESIS] shape walk of `{ty}` reached its depth cap of {SHAPE_DEPTH_CAP}: opaque"
            );
        }
    }
    shape
}

/// The state of one [`shape_of`] walk: the types being walked (see [`shape_rec`]), the
/// visits left of [`SHAPE_NODE_BUDGET`], and whether some branch reached
/// [`SHAPE_DEPTH_CAP`] (diagnostics only).
struct ShapeWalk<'tcx> {
    stack: Vec<(Ty<'tcx>, bool)>,
    budget: u32,
    depth_exhausted: bool,
}

fn normalized<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Unnormalized<'tcx, Ty<'tcx>>,
) -> Option<Ty<'tcx>> {
    tcx.try_normalize_erasing_regions(typing_env, ty).ok()
}

/// The shape of an alias that survived normalization in the body's environment.
/// Only an alias still rooted in a type or const parameter is [`Shape::Generic`]:
/// its value is chosen by the instantiation and the generic model holds none. An
/// alias that mentions no parameter yet did not normalize (an opaque `impl Trait`,
/// an unnormalizable projection) is something the walk cannot see through, so it
/// is [`Shape::Opaque`] and refused.
pub(super) fn alias_shape(rooted_in_param: bool, opaque_type: bool) -> Shape {
    if rooted_in_param && !opaque_type { Shape::Generic } else { Shape::Opaque }
}

/// `walk.stack` holds the types being walked, each with whether it was ENTERED
/// through a reference or an `UnsafeCell` (`barrier`), the only constructors at which
/// [`reach`] changes its access context. Every visit spends one unit of
/// `walk.budget`; a visit with none left is [`Shape::Opaque`] (refused).
fn shape_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    depth: u32,
    barrier: bool,
    walk: &mut ShapeWalk<'tcx>,
) -> Shape {
    let Some(depth) = depth.checked_sub(1) else {
        walk.depth_exhausted = true;
        return Shape::Opaque;
    };
    let Some(budget) = walk.budget.checked_sub(1) else { return Shape::Opaque };
    walk.budget = budget;
    let stack = &mut walk.stack;
    if let Some(ancestor) = stack.iter().position(|(seen, _)| *seen == ty) {
        // Trust (OD-1 item 18, 2026-10-06): a RECURSIVE type (`enum Sort { Seq(Box<Sort>),
        // .. }`, `struct Node { kids: Vec<Node> }`). When no reference or `UnsafeCell`
        // lies between the ancestor occurrence and this one, [`reach`] visits this
        // subtree in exactly the access context of the ancestor, whose own walk is
        // already collecting every flag the subtree can raise, so the back edge adds
        // nothing and is `Plain`. Across a reference or a cell the context may differ:
        // still `Opaque` (refused), as every cycle was before.
        let same_context = !barrier && stack[ancestor + 1..].iter().all(|(_, b)| !*b);
        return if same_context { Shape::Plain } else { Shape::Opaque };
    }
    stack.push((ty, barrier));
    let sub = |ty: Ty<'tcx>, walk: &mut ShapeWalk<'tcx>| {
        shape_rec(tcx, typing_env, ty, depth, false, walk)
    };
    let sub_barrier = |ty: Ty<'tcx>, walk: &mut ShapeWalk<'tcx>| {
        shape_rec(tcx, typing_env, ty, depth, true, walk)
    };
    let shape = match *ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => Shape::Plain,
        ty::FnDef(..) | ty::FnPtr(..) => Shape::Plain,
        ty::Str => Shape::Str,
        ty::Param(_) => Shape::Generic,
        ty::Alias(_, ty::AliasTy { kind: ty::Opaque { .. }, .. }) => alias_shape(false, true),
        ty::Alias(..) => alias_shape(ty.has_non_region_param(), false),
        ty::Ref(_, pointee, mutbl) => {
            Shape::Ref { mutable: mutbl.is_mut(), pointee: Box::new(sub_barrier(pointee, walk)) }
        }
        ty::RawPtr(..) => Shape::RawPtr,
        ty::Array(element, _) => Shape::Fields(vec![sub(element, walk)]),
        ty::Slice(element) => Shape::Slice(Box::new(sub(element, walk))),
        ty::Tuple(fields) => Shape::Fields(fields.iter().map(|field| sub(field, walk)).collect()),
        ty::Adt(adt, args) => {
            if adt.is_box() {
                Shape::Owned(Box::new(sub(args.type_at(0), walk)))
            } else if adt.is_unsafe_cell() {
                Shape::UnsafeCell(Box::new(sub_barrier(args.type_at(0), walk)))
            } else if adt.is_phantom_data() {
                Shape::Fields(vec![sub(args.type_at(0), walk)])
            } else if tcx.is_lang_item(adt.did(), rustc_attr_ir::lang_items::LangItem::NonNull) {
                Shape::RawPtr
            } else if is_core_unique(tcx, adt.did()) {
                Shape::Owned(Box::new(sub(args.type_at(0), walk)))
            } else if is_alloc_raw_vec_inner(tcx, adt.did()) {
                // The erased allocation bytes; the element type is shaped
                // through the enclosing `RawVec`'s `PhantomData<T>`.
                Shape::Owned(Box::new(Shape::Plain))
            } else {
                // `FieldDef::ty` substitutes the ADT's arguments into the declared
                // field type WITHOUT normalizing it: `struct P { p: <*mut u8 as
                // Id>::Out }` must shape as the raw pointer it is.
                Shape::Fields(
                    adt.all_fields()
                        .map(|field| match normalized(tcx, typing_env, field.ty(tcx, args)) {
                            Some(field_ty) => sub(field_ty, walk),
                            None => Shape::Opaque,
                        })
                        .collect(),
                )
            }
        }
        ty::Closure(_, args) => {
            Shape::Fields(args.as_closure().upvar_tys().iter().map(|ty| sub(ty, walk)).collect())
        }
        // Trust (OD-1 item 18, 2026-10-06): a PATTERN TYPE is its base type's bits
        // under a validity restriction (`pattern_type!(usize is 0..=MAX/2)`, the
        // capacity inside every `RawVec`, so every `String`/`Vec`;
        // `pattern_type!(*const T is !null)`, inside `NonNull`): whatever a callee
        // can reach or write through one, it can through the base, and nothing
        // more. Shaped AS ITS BASE — a scalar base is `Plain`, a raw-pointer base
        // `RawPtr` (still refused). Before, `ty::Pat` fell to `Opaque`, so `&String`,
        // `&Vec<_>` and a by-value `String` were refused at every site.
        ty::Pat(base, _) => sub(base, walk),
        _ => Shape::Opaque,
    };
    walk.stack.pop();
    shape
}

// ---------------------------------------------------------------------------
// Admission over one body.
// ---------------------------------------------------------------------------

/// One admitted site of a root body.
pub(super) struct AdmittedSite {
    pub(super) block: BasicBlock,
    /// The exact callee spelling the bridge sees (`func_operand_name`), or the
    /// reserved `trust_types::TRUST_INDIRECT_CALLEE_PATH` at a pointer site.
    pub(super) call_key: String,
    /// The bridge's argument indices whose pointee is havocked (at a pointer site the
    /// bridge's argument 0 is the fn-pointer value, so every index is shifted by one).
    pub(super) havoc_args: Vec<usize>,
    /// The open trait item the call dispatches: the callee written at a direct call,
    /// the item this body reified the pointer from at a pointer site.
    pub(super) callee: DefId,
    /// The dispatched item as `func_operand_name` spells it (the row text; equal to
    /// `call_key` at a direct site).
    pub(super) dispatched: String,
    /// Whether the call goes through a fn pointer this body reified from `callee`.
    pub(super) through_pointer: bool,
}

/// Whether every type and const parameter `args` mentions is one of `def`'s own
/// generics (its own or its parent's), and nothing is an inference variable, a
/// placeholder, an escaping bound variable, an error or an opaque `impl Trait`.
fn mentions_only_own_params<'tcx>(tcx: TyCtxt<'tcx>, def: DefId, args: GenericArgs<'tcx>) -> bool {
    let generics = tcx.generics_of(def);
    let own = |index: u32, name: rustc_span::Symbol| {
        (index as usize) < generics.count() && generics.param_at(index as usize, tcx).name == name
    };
    args.iter().all(|arg| {
        arg.walk().all(|inner| {
            if let Some(ty) = inner.as_type() {
                match *ty.kind() {
                    ty::Param(param) => own(param.index, param.name),
                    ty::Infer(_)
                    | ty::Placeholder(_)
                    | ty::Bound(..)
                    | ty::Error(_)
                    | ty::Alias(_, ty::AliasTy { kind: ty::Opaque { .. }, .. }) => false,
                    _ => true,
                }
            } else if let Some(ct) = inner.as_const() {
                match ct.kind() {
                    ty::ConstKind::Param(param) => own(param.index, param.name),
                    ty::ConstKind::Infer(_)
                    | ty::ConstKind::Placeholder(_)
                    | ty::ConstKind::Bound(..)
                    | ty::ConstKind::Error(_) => false,
                    _ => true,
                }
            } else {
                true
            }
        })
    })
}

/// Does `body` mention its own fn item at arguments other than its identity
/// arguments (polymorphic recursion, which no instance inventory bounds)?
fn polymorphic_self_mention<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    let own = body.source.def_id();
    let identity = ty::GenericArgs::identity_for_item(tcx, own);
    fn_item_mentions(tcx, body).into_iter().any(|(def, args, _)| def == own && args != identity)
}

/// Every fn item named in `body`'s statements and terminators (a call's callee, or
/// any other mention), in MIR order, with its span.
fn fn_item_mentions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(DefId, GenericArgs<'tcx>, Span)> {
    struct Mentions<'tcx> {
        out: Vec<(DefId, GenericArgs<'tcx>, Span)>,
    }
    impl<'tcx> Visitor<'tcx> for Mentions<'tcx> {
        fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _location: Location) {
            if let ty::FnDef(def, args) = *constant.const_.ty().peel_refs().kind() {
                self.out.push((def, args.skip_binder(), constant.span));
            }
        }
    }
    let _ = tcx; // the visitor needs no queries
    let mut mentions = Mentions { out: Vec::new() };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        mentions.visit_basic_block_data(block, data);
    }
    mentions.out
}

/// The body conjuncts of design §2.3 for the ROOT body `body` (`func` is its
/// extracted form, for D33's census): a plain local `fn`/assoc `fn` (not Clean
/// origin, not a promoted), no unsafe operation, no polymorphic recursion.
fn root_body_admits<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &trust_types::VerifiableFunction,
) -> bool {
    let def = body.source.def_id();
    let is_plain_fn = body.source.promoted.is_none()
        && def.as_local().is_some_and(|local| {
            (matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn)
                || is_plain_closure_of_fn(tcx, def))
                && !crate::clean_origin_mir::is_clean_origin(tcx, local)
        });
    if !is_plain_fn {
        return false;
    }
    // Trust (OD-1 item 18): reference-target casts are relaxed only when the MIR shows
    // each is an unsizing coercion. Trust (OD-1 T-D, 2026-10-12): the `format_args!`
    // desugaring's own `Arguments::new` calls are not counted, only at the blocks
    // `format_args_ctor_call_blocks` proved on MIR and HIR (with neither relaxation
    // the census is `body_has_unsafe_operation` exactly).
    let modulo_ref_unsize = reference_casts_are_unsize(body);
    let format_args_ctor_blocks = format_args_ctor_call_blocks(tcx, body);
    let census = trust_vcgen::body_has_unsafe_operation_modulo_format_args(
        func,
        modulo_ref_unsize,
        &format_args_ctor_blocks,
    );
    let unsafe_operation = census
        || super::def_uses_user_unsafe_source(tcx, def)
        || super::function_uses_unsafe_outside_std(tcx, body);
    let decision = body_admits(is_plain_fn, unsafe_operation, polymorphic_self_mention(tcx, body));
    if super::env_flag_enabled("TRUST_INSTANCE_HYPOTHESIS_DEBUG") && decision.is_err() {
        // Diagnostics only: the census arm that fired (OD-1 T3, 2026-10-10).
        let witness = trust_vcgen::body_unsafe_operation_witness_modulo_format_args(
            func,
            modulo_ref_unsize,
            &format_args_ctor_blocks,
        );
        eprintln!(
            "[INSTANCE_HYPOTHESIS] {}: body refused: {:?} (census {census}, witness {witness:?})",
            func.def_path, decision
        );
    }
    decision.is_ok()
}

/// Trust (OD-1 item 20, T6, 2026-10-10; DECISION_QUEUE "OD-1-T6-CALLABLE"): whether
/// the local body `def` is a PLAIN CLOSURE (its type is `ty::Closure`: not a
/// coroutine, not an async closure) whose typeck root is a local plain `fn`/assoc
/// `fn` that is not Clean origin. Such a body is a function whose first argument is
/// its environment (the captures), and its generics ARE its typeck root's: its
/// instance at a concrete root instance `f::<τ>` is `{closure}::<τ, ..>`, so an open
/// dispatch `<F as FnMut<A>>::call_mut` on a captured `F` is the same per-instance
/// dispatch as in `f` itself, discharged where `f::<τ>`'s glue walk reaches the
/// closure (`glue::discharge_glue_of_instance`, `local_bodies_in_args`) or where a
/// body names the closure's call at a concrete instance. Every other admission
/// conjunct (unsafe census, argument shapes, own-params-only) is asked unchanged.
fn is_plain_closure_of_fn(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if !tcx.is_closure_like(def) || tcx.is_coroutine(def) {
        return false;
    }
    if !matches!(
        tcx.type_of(def).instantiate_identity().skip_normalization().kind(),
        ty::Closure(..)
    ) {
        return false;
    }
    let root = tcx.typeck_root_def_id(def);
    root.as_local().is_some_and(|local| {
        matches!(tcx.def_kind(local), DefKind::Fn | DefKind::AssocFn)
            && !crate::clean_origin_mir::is_clean_origin(tcx, local)
    })
}

/// Trust (OD-1 item 18, 2026-10-06): whether EVERY cast in `body` whose target is a
/// reference is an UNSIZING coercion (`PointerCoercion::Unsize`: `&[T; N] -> &[T]`,
/// `&C -> &dyn Tr`). Such a coercion is safe code — it writes nothing and only
/// attaches a length or a vtable to the source pointer — but the extracted body's
/// `Rvalue::Cast` carries no cast kind, so D33's census counts it as an unsafe
/// operation (an extractor transmute leg can also emit a reference-typed `Cast`).
/// When this holds, every reference-target `Cast` in the extracted body came from
/// such a coercion and the census may skip that one arm
/// (`trust_vcgen::body_has_unsafe_operation_modulo_ref_unsize`); otherwise the full
/// census answers. `body` is the `optimized_mir` the body was extracted from,
/// inlined callees included.
fn reference_casts_are_unsize(body: &Body<'_>) -> bool {
    use rustc_middle::mir::{CastKind, Rvalue, StatementKind};
    body.basic_blocks.iter().flat_map(|data| data.statements.iter()).all(|stmt| {
        let StatementKind::Assign(boxed) = &stmt.kind else { return true };
        match &boxed.1 {
            Rvalue::Cast(kind, _, target) if target.is_ref() => matches!(
                kind,
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _)
            ),
            _ => true,
        }
    })
}

/// Trust (OD-1 T-D, 2026-10-12): the blocks of `body` whose `Call` terminator is the
/// `format_args!` desugaring's own call to `core::fmt::Arguments::new`, which D33's
/// census otherwise counts as "a call to an unsafe-signature function" and so refused
/// the WHOLE body of every generic `fn` that formats anything (`format!`, `write!`,
/// `panic!` with an argument): MEASURED on preview4's stage 1 (`35a39d5c74`), nn-glm5
/// `Glm5MLP::load` and `Glm5Model::load` and nn-qwen3 `Qwen3Model::load` and
/// `Qwen3MoeModel::load` kept their `<impl AsRef<VarBuilder>>::as_ref` site as a class
/// (c) `failed` row for this alone, while their siblings without a `format!` were
/// admitted.
///
/// A block is listed only when ALL hold, each fail-closed:
/// * the callee is a fn item whose parent is the impl carrying
///   `#[rustc_diagnostic_item = "FmtArgumentsNew"]`, that impl is in an authenticated
///   sysroot crate (`def_is_in_real_sysroot_crate`, never a name), and the item is
///   `new` (the impl's only unsafe fn);
/// * the call's `fn_span` is the span of a call inside an
///   `UnsafeSource::CompilerGenerated` block of this body's own HIR
///   (`inlined_unsafe_evidence::compiler_generated_unsafe_call_spans`, the exemption
///   the inlined-unsafe row and `def_uses_user_unsafe_source` already draw): a user's
///   `unsafe { Arguments::new(..) }` (nightly `fmt_internals`) is `UserProvided` and is
///   not listed, and a span mismatch of any kind lists nothing;
/// * trust-vcgen additionally requires the extracted callee to render as the
///   crate-anchored constructor (`is_std_fmt_arguments_ctor`).
///
/// Why this is the same claim the census protects: the census exists because the
/// havoc that replaces an admitted call cannot model a body whose safety invariant
/// depends on what the callee does (design §3). `Arguments::new`'s only safety
/// precondition is that its template and argument array encode a valid
/// `fmt::Arguments`, which the desugaring that wrote the call upholds by construction
/// whatever any open dispatch does; its body is two transmutes of live references into
/// `NonNull`, with no memory access and no panic. Running the formatter (and any user
/// `Display`/`Debug` panic) is a separate call keeping its own row, and an
/// `Arguments` value handed to an open dispatch is still judged by `decide_arg` (its
/// `NonNull` fields refuse it). Every other census arm and every other unsafe call is
/// unchanged. A body the MIR inliner copied `Arguments::new` into has no such call
/// (its transmutes meet the census's cast arm) and stays refused.
fn format_args_ctor_call_blocks<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<usize> {
    let Some(local) = body.source.def_id().as_local() else { return Vec::new() };
    if body.source.promoted.is_some() {
        return Vec::new();
    }
    let Some(ctor_impl) = tcx.get_diagnostic_item(sym::FmtArgumentsNew) else {
        return Vec::new();
    };
    if !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, ctor_impl) {
        return Vec::new();
    }
    let mut generated: Option<FxHashSet<Span>> = None;
    let mut blocks = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { func, fn_span, .. } = &data.terminator().kind else {
            continue;
        };
        let ty::FnDef(callee, _) = *func.ty(&body.local_decls, tcx).kind() else { continue };
        if tcx.opt_parent(callee) != Some(ctor_impl) || tcx.item_name(callee) != sym::new {
            continue;
        }
        let generated = generated.get_or_insert_with(|| {
            super::inlined_unsafe_evidence::compiler_generated_unsafe_call_spans(tcx, local)
        });
        if generated.contains(fn_span) {
            blocks.push(block.as_usize());
        }
    }
    blocks
}

/// Trust (OD-1 item 18, 2026-10-06): the decision for one argument of a candidate
/// site. [`decide_arg`] on the argument's own type, except for a SHARED TRAIT-OBJECT
/// REFERENCE this body built itself: an argument `&dyn Tr` whose operand is a local
/// with exactly one definition, an unsizing coercion `&C as &dyn Tr`
/// ([`sole_unsize_source`]), is decided on the SOURCE type `&C`. The fat pointer the
/// callee receives is `&C`'s data pointer plus `C`'s vtable — chosen by this body's
/// own types — so every place the callee can reach or write through it, it can reach
/// through `&C`. Only an `Inert` decision is taken: the bridge stores a havoc through
/// a pointee it can type, and a `dyn` pointee is not one, so a source that needs a
/// havoc (interior mutability) is refused. A trait object the body did not build
/// (an argument, a field, a reseated local) keeps the opaque decision (refused).
fn decide_site_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    arg: &rustc_middle::mir::Operand<'tcx>,
) -> ArgDecision {
    let arg_ty = arg.ty(&body.local_decls, tcx);
    let direct = decide_arg(&shape_of(tcx, typing_env, arg_ty));
    let ArgDecision::Refuse(_) = direct else { return direct };
    let ty::Ref(_, pointee, rustc_middle::mir::Mutability::Not) = *arg_ty.kind() else {
        return direct;
    };
    if !matches!(pointee.kind(), ty::Dynamic(..)) {
        return direct;
    }
    let Some(source_ty) = sole_unsize_source(tcx, body, arg) else { return direct };
    match decide_arg(&shape_of(tcx, typing_env, source_ty)) {
        ArgDecision::Inert => ArgDecision::Inert,
        ArgDecision::Havoc => ArgDecision::Refuse(
            "a trait object built from a value the callee may write through interior \
             mutability (no havoc reaches a `dyn` pointee)",
        ),
        refused @ ArgDecision::Refuse(_) => refused,
    }
}

/// Trust (OD-1 item 18): the source type of the unsizing coercion that is the ONLY
/// definition of the whole local `operand` reads: the local is not an argument, has
/// exactly one assignment in the body and it is a `PointerCoercion::Unsize` cast, is
/// never borrowed or has its address taken, and no call writes it (the structural
/// conditions of `sole_reified_constant_of_callee`). `None` for every other shape.
fn sole_unsize_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &rustc_middle::mir::Operand<'tcx>,
) -> Option<Ty<'tcx>> {
    use rustc_middle::mir::{CastKind, Operand, Rvalue, StatementKind};
    let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
    if !place.projection.is_empty() || place.local.as_usize() <= body.arg_count {
        return None;
    }
    let local = place.local;
    let mut source = None;
    let mut assignments = 0usize;
    for data in body.basic_blocks.iter() {
        for stmt in data.statements.iter() {
            match &stmt.kind {
                StatementKind::Assign(boxed) => {
                    let (dest, rvalue) = &**boxed;
                    if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue
                        && borrowed.local == local
                    {
                        return None;
                    }
                    if dest.local != local {
                        continue;
                    }
                    if !dest.projection.is_empty() {
                        return None;
                    }
                    assignments += 1;
                    source = match rvalue {
                        Rvalue::Cast(
                            CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _),
                            from,
                            _,
                        ) => Some(from.ty(&body.local_decls, tcx)),
                        _ => None,
                    };
                }
                StatementKind::SetDiscriminant { place: written, .. } if written.local == local => {
                    return None;
                }
                _ => {}
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && destination.local == local
        {
            return None;
        }
    }
    if assignments == 1 { source } else { None }
}

/// The open trait item an indirect call's fn-pointer operand was reified from in
/// this body (`let p: fn(&T) -> u32 = T::m; p(t)`), when the value is pinned to it
/// (`super::sole_reified_constant_of_callee`: one whole local, one `ReifyFnPointer`
/// assignment from a constant, never borrowed, never written by a call), with the
/// constant operand itself (for its call-key spelling).
fn reified_dispatch<'a, 'tcx>(
    body: &'a Body<'tcx>,
    callee: &rustc_middle::mir::Operand<'tcx>,
) -> Option<(DefId, GenericArgs<'tcx>, &'a ConstOperand<'tcx>)> {
    let constant = super::sole_reified_constant_of_callee(body, callee)?;
    match *constant.const_.ty().kind() {
        ty::FnDef(def, args) => Some((def, args.skip_binder(), constant)),
        _ => None,
    }
}

/// The admitted sites of the ROOT body `body` (design §2.3). `func` is its extracted
/// form (for D33's census); `decided_elsewhere(call_key)` answers whether one of the
/// bundle's other classifications already owns the call key. Empty when the body
/// conjuncts refuse.
///
/// Two call shapes dispatch an open trait item at the body's own parameters:
/// * a DIRECT call `<P as Tr>::m(..)`;
/// * Trust (OD-1, 2026-10-04, open shapes) a call THROUGH A FN POINTER this body
///   reified from such an item (`let p: fn(&T) -> u32 = T::m; p(t)`): at every
///   instance `τ` the pointer IS `<τ as Tr>::m`, so the call is the same open
///   dispatch and gets the same hypothesis and discharge. Before, it carried no row
///   at all (a `native-verification-gap` `unknown`, refused by the indirect-call
///   gate). The extractor spells the call `TRUST_INDIRECT_CALLEE_PATH` with the
///   pointer as argument 0, so the bridge's havoc indices are shifted by one. Only a
///   call with a normal-return target: a diverging indirect call is opaque to the
///   extractor and never reaches the bridge's admitted arm.
pub(super) fn admitted_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &trust_types::VerifiableFunction,
    decided_elsewhere: impl Fn(&str) -> bool,
) -> Vec<AdmittedSite> {
    if !root_body_admits(tcx, body, func) {
        return Vec::new();
    }
    let def = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, def);
    let mut sites = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(dispatch) = open_dispatch_at(tcx, body, typing_env, block) else { continue };
        let args = match &data.terminator().kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args,
            _ => continue,
        };
        let decisions: Vec<ArgDecision> =
            args.iter().map(|arg| decide_site_arg(tcx, body, typing_env, &arg.node)).collect();
        let decision = site_admits(
            true,
            dispatch.own_params_only,
            decided_elsewhere(&dispatch.dispatched),
            &decisions,
        );
        if super::env_flag_enabled("TRUST_INSTANCE_HYPOTHESIS_DEBUG") {
            eprintln!(
                "[INSTANCE_HYPOTHESIS] {}: site `{}` at bb{}: {:?} (own params only: {})",
                func.def_path,
                dispatch.dispatched,
                block.as_u32(),
                decision,
                dispatch.own_params_only
            );
        }
        if let Ok(havoc_args) = decision {
            let shift = usize::from(dispatch.through_pointer);
            sites.push(AdmittedSite {
                block,
                call_key: dispatch.call_key,
                havoc_args: havoc_args.into_iter().map(|index| index + shift).collect(),
                callee: dispatch.callee,
                dispatched: dispatch.dispatched,
                through_pointer: dispatch.through_pointer,
            });
        }
    }
    sites
}

/// An unresolved trait-method dispatch at one call of a generic body, before any
/// admission conjunct is asked ([`open_dispatch_at`]).
struct OpenDispatch {
    /// The open trait item the call dispatches (at a pointer site, the item the body
    /// reified the pointer from).
    callee: DefId,
    /// The call key the bridge sees (`TRUST_INDIRECT_CALLEE_PATH` at a pointer site).
    call_key: String,
    /// The dispatched item as `func_operand_name` spells it.
    dispatched: String,
    through_pointer: bool,
    /// Whether the dispatch's generic arguments mention only the body's own
    /// parameters (`mentions_only_own_params`).
    own_params_only: bool,
}

/// The open trait-method dispatch at the call terminating `block` of `body`, if
/// any: a DIRECT call `<P as Tr>::m(..)`, or a call with a normal-return target
/// THROUGH A FN POINTER pinned to such an item (`reified_dispatch`), whose
/// `Instance::try_resolve` in `typing_env` (the body's own) answers `Ok(None)`.
/// The one structural classifier of both phases: phase 1 asks it of a LOCAL root
/// body ([`admitted_sites`], which then applies the admission conjuncts), phase 2 of
/// a dependency's generic body re-read from its encoded MIR
/// ([`foreign_carrier_records`], which applies none of them: every such dispatch is
/// discharged at every instance this compilation names).
fn open_dispatch_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    block: BasicBlock,
) -> Option<OpenDispatch> {
    let def = body.source.def_id();
    let (callee, has_target) = match &body.basic_blocks[block].terminator().kind {
        TerminatorKind::Call { func: callee, target, .. } => (callee, target.is_some()),
        TerminatorKind::TailCall { func: callee, .. } => (callee, true),
        _ => return None,
    };
    let (callee_def, generic_args, dispatched, through_pointer) =
        if let Some((callee_def, generic_args)) = callee.const_fn_def() {
            let key = trust_mir_extract::func_operand_name_in_body(tcx, body, callee);
            (callee_def, generic_args, key, false)
        } else if has_target
            && matches!(callee.ty(&body.local_decls, tcx).kind(), ty::FnPtr(..))
            && let Some((callee_def, generic_args, constant)) = reified_dispatch(body, callee)
        {
            let operand = rustc_middle::mir::Operand::Constant(Box::new(constant.clone()));
            let key = trust_mir_extract::func_operand_name_in_body(tcx, body, &operand);
            (callee_def, generic_args, key, true)
        } else {
            return None;
        };
    let unresolved_trait_dispatch = tcx.trait_of_assoc(callee_def).is_some()
        && matches!(ty::Instance::try_resolve(tcx, typing_env, callee_def, generic_args), Ok(None));
    if !unresolved_trait_dispatch {
        return None;
    }
    let call_key = if through_pointer {
        trust_types::TRUST_INDIRECT_CALLEE_PATH.to_string()
    } else {
        dispatched.clone()
    };
    Some(OpenDispatch {
        callee: callee_def,
        call_key,
        dispatched,
        through_pointer,
        own_params_only: mentions_only_own_params(tcx, def, generic_args),
    })
}

// ---------------------------------------------------------------------------
// The session ledger.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum SiteKind {
    /// An admitted call in this body.
    Direct,
    /// Trust (OD-1, 2026-10-04, open shapes): an admitted call through a fn pointer
    /// this body reified from the open trait item `SiteRecord::callee`
    /// ([`admitted_sites`]). Discharged exactly as [`SiteKind::Direct`], reading the
    /// item off the reification instead of off the call.
    Pointer,
    /// A call that RESOLVES (in this body's typing environment) to the local generic
    /// body `callee` that carries hypotheses, at arguments still generic here:
    /// `callee`'s sites, substituted, are this body's hypotheses too. `callee` is the
    /// resolved body (an impl's method, not the trait item the call names).
    ///
    /// Trust (OD-1, 2026-10-04, open shapes): `admitted` when the bridge lowers the
    /// call under those propagated hypotheses ([`via_call_admits`]): the callee's own
    /// rows prove everything but its hypotheses (the instance-RELATIVE bar), so the
    /// call adds no obligation the propagated rows do not name. Not admitted, the call
    /// keeps its absent-callee row (phase 1's behaviour).
    Via { callee: DefId, admitted: bool },
    /// Trust (OD-1 phase 2 review fix, 2026-10-05): a DEPENDENCY generic body runs
    /// code at its instances that this compilation does not re-derive as sites — a
    /// still-generic call that leaves the declared scope (a sysroot or undeclared
    /// generic, a closure, a shim), drop glue of a parameter-mentioning type,
    /// unsizing or reifying one, a fn item at its parameters handed on as a value,
    /// or an open dispatch at arguments that are not its own parameters. ONE record
    /// per body (block [`OPAQUE_SITE_BLOCK`]); `call_key` says what it is. Its
    /// discharge is `unknown` at every instance: the ruling's "unresolvable fails
    /// closed" for what the site inventory cannot see, instead of a silent drop.
    /// Never in the LOCAL ledger: a local body's reach is verified here.
    Opaque,
}

/// Trust (OD-1 phase 2 review fix): the block number a [`SiteKind::Opaque`] record
/// carries. No MIR body has this many blocks, so its discharge key can never
/// collide with a real site's.
const OPAQUE_SITE_BLOCK: u32 = u32::MAX;

/// Trust (regression `discharge-cycle`): the block number the discharge key of an
/// [`unverified_cycle_generic`] row carries; like [`OPAQUE_SITE_BLOCK`], no MIR body
/// has this many blocks.
const UNVERIFIED_CYCLE_GENERIC_BLOCK: u32 = u32::MAX - 1;

#[derive(Clone, Debug)]
struct SiteRecord {
    /// The MIR block whose terminator is the call, in the body the verifier walked
    /// (the final `optimized_mir`; `TrustVerify` is that pipeline's last pass).
    block: u32,
    /// The callee `DefId` written at the call (at a pointer site, the reified item).
    callee: DefId,
    kind: SiteKind,
    span: Span,
    /// The callee as the bridge spells it (at a pointer site, the reified item as a
    /// direct call would spell it), for the row text.
    call_key: String,
    /// The call key the zero-obligation transport decision may treat as accounted
    /// for by this record's hypothesis rows (`admitted_site_call_keys`); `None` when
    /// the bridge did not lower the call under the hypothesis.
    accounted_key: Option<String>,
}

/// Per crate compilation: which bodies carry hypotheses, and which discharges were
/// already published (keyed by the INTERNED instance arguments, see the module doc).
#[derive(Default)]
pub(super) struct InstanceHypothesisLedger {
    sites: FxHashMap<DefId, Vec<SiteRecord>>,
    published_discharges: FxHashSet<(DefId, u32, usize)>,
    inventory_row_published: bool,
    /// Trust (OD-1 phase 2): a dependency generic's open-dispatch sites and its
    /// still-generic calls into other dependency generics, re-read from its encoded
    /// MIR ([`foreign_scan`]); `None` when the body is out of the declared scope.
    foreign_scans: FxHashMap<DefId, Option<ForeignScan>>,
    /// Trust (OD-1 phase 2): whether a dependency generic reaches an open-dispatch
    /// site through its still-generic calls ([`foreign_reaches_site`]).
    foreign_reaches: FxHashMap<DefId, bool>,
}

/// Trust (OD-1 phase 2): what one dependency generic body holds, re-read from its
/// encoded MIR: every open trait-method dispatch at its own parameters (`direct`,
/// [`SiteKind::Direct`] / [`SiteKind::Pointer`]) and every call that resolves, in its
/// own typing environment and at arguments still generic there, to another
/// dependency generic in the declared scope (`edges`, [`SiteKind::Via`]). An edge
/// becomes a site record only when its target reaches a site.
#[derive(Clone, Debug)]
struct ForeignScan {
    direct: Vec<SiteRecord>,
    edges: Vec<SiteRecord>,
}

fn with_ledger<R>(
    sess: &rustc_session::Session,
    f: impl FnOnce(&mut InstanceHypothesisLedger) -> R,
) -> R {
    sess.with_trust_compiler_state::<InstanceHypothesisLedger, _>(f)
}

/// The bodies that carry a hypothesis so far in this compilation. A set: membership
/// only, so the map's iteration order cannot reach any output.
fn carrier_set(sess: &rustc_session::Session) -> FxHashSet<DefId> {
    with_ledger(sess, |ledger| {
        // Collected into a set and only tested for membership: the order is unused.
        #[allow(rustc::potential_query_instability)]
        let carriers: FxHashSet<DefId> = ledger.sites.keys().copied().collect();
        carriers
    })
}

/// The hypothesis-carrying body that `def` at `args` RESOLVES to in `typing_env`,
/// with the instance's own arguments. A mention names what the source wrote — for a
/// trait-impl or default method that is the TRAIT ITEM, never the impl's method the
/// ledger holds — so the carrier test must run on the resolved `InstanceKind::Item`.
/// Anything else (unresolved, a shim, a virtual call, a body that carries no
/// hypothesis) is `None`. `is_carrier` answers for the resolved item ([`Carriers`]).
fn resolved_carrier<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def: DefId,
    args: GenericArgs<'tcx>,
    is_carrier: &impl Fn(DefId) -> bool,
) -> Option<(DefId, GenericArgs<'tcx>)> {
    match ty::Instance::try_resolve(tcx, typing_env, def, args) {
        Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) if is_carrier(item) => {
            Some((item, args))
        }
        _ => None,
    }
}

/// The carrier test of both phases: a LOCAL body carries a hypothesis when the
/// ledger holds its records (phase 1, filled in verification order); a DEPENDENCY
/// generic in the declared scope carries one when its re-read MIR reaches an open
/// dispatch at its own parameters (phase 2, [`foreign_carrier_records`]).
struct Carriers {
    local: FxHashSet<DefId>,
}

impl Carriers {
    fn snapshot(sess: &rustc_session::Session) -> Self {
        Carriers { local: carrier_set(sess) }
    }

    fn contains(&self, tcx: TyCtxt<'_>, item: DefId) -> bool {
        if item.is_local() {
            self.local.contains(&item)
        } else {
            foreign_carrier_records(tcx, item).is_some_and(|records| !records.is_empty())
        }
    }
}

/// The site records of the carrier `def`: the ledger's for a local body, the
/// re-derived ones for a dependency generic. `None` when `def` carries none.
fn carrier_records(tcx: TyCtxt<'_>, def: DefId) -> Option<Vec<SiteRecord>> {
    if def.is_local() {
        with_ledger(tcx.sess, |ledger| ledger.sites.get(&def).cloned())
    } else {
        foreign_carrier_records(tcx, def).filter(|records| !records.is_empty())
    }
}

// ---------------------------------------------------------------------------
// Phase 2: a dependency's generic bodies, re-derived from its encoded MIR.
// ---------------------------------------------------------------------------

/// Trust (OD-1 phase 2, 2026-10-05): how many distinct dependency generic bodies one
/// reachability question may visit ([`foreign_reaches_site`]). Past it the answer is
/// `true` (fail-closed: the edge stays a propagated site, and a discharge through a
/// body that turns out to carry nothing fails closed instead of passing silently).
const FOREIGN_REACH_NODE_CAP: usize = 256;

/// Trust (OD-1 phase 2): is the dependency body `def` one whose MIR this compilation
/// may READ for instance-hypothesis sites? D4's channel, nothing new: the crate is in
/// the build-declared bundling scope by IDENTITY and statically linked
/// (`declared_bundle_scope_subject`, the conjuncts (1)–(2) of
/// `foreign_rederivation`), it is not the sysroot (conjunct (3)), and the item is a
/// `fn`/assoc `fn` with encoded MIR (conjunct (4)) that is GENERIC (only a generic
/// body has an instance this compilation creates). No dependency verdict, policy or
/// `-Ztrust-verify` setting is read: a verify-off, advisory and strict dependency are
/// indistinguishable here, and so is a dependency that disagrees with itself about
/// what it admitted. Conjuncts (5)–(7) are not asked: they bound CREDIT for a body,
/// and a site read from a body grants none — it only adds discharge rows.
fn foreign_site_scope(tcx: TyCtxt<'_>, def: DefId) -> bool {
    !def.is_local()
        && super::declared_bundle_scope_subject(tcx, def)
        && super::foreign_rederivation::declared_scope_bucket_is_rederivable(
            trust_mir_extract::policy::classify_def(tcx, def, super::step4_library_lane()),
        )
        && matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx.generics_of(def).requires_monomorphization(tcx)
        && tcx.is_mir_available(def)
}

/// Trust (OD-1 phase 2 review fix, 2026-10-05): is `def` a DEPENDENCY item whose
/// `#[trust::assume_total]` / user-axiom attribute a call in THIS compilation must
/// not spend? Every non-local item with a TYPE parameter (its own, an enclosing
/// impl's or trait's, `Self` included). Its instance is created here, at types the
/// dependency's author never audited the body at, and an axiom "total for every
/// instantiation" over open dispatch is the claim OD-1 says is false by
/// construction; D4 reads no claim a dependency makes about itself. Read anyway,
/// it removed the call's own row, and a panicking instance reached through a
/// closure, a `dyn`, a sysroot generic, drop glue or a third crate built rc=0
/// under `-Ztrust-policy=certify` (review of 2026-10-05; the binary panicked). The
/// call keeps its fail-closed absent-callee row instead. Lifetime- and
/// const-only generics, a non-generic dependency item and every local item are
/// unchanged (`AssumedTotalCalleeAssumption`, docs/TCB.md).
pub(super) fn dependency_generic_axiom_is_not_read(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if def.is_local() {
        return false;
    }
    let mut generics = Some(tcx.generics_of(def));
    while let Some(current) = generics {
        if current
            .own_params
            .iter()
            .any(|param| matches!(param.kind, ty::GenericParamDefKind::Type { .. }))
        {
            return true;
        }
        generics = current.parent.map(|parent| tcx.generics_of(parent));
    }
    false
}

/// Trust (OD-1 phase 2): the [`ForeignScan`] of the dependency generic `def`, cached
/// per compilation. Every open dispatch is a site, ADMITTED by the dependency or not:
/// the admission conjuncts (unsafe fence, argument shapes, rung 1/2, D4-B) decide
/// what the dependency's OWN rows claim, and none of them is a property of the
/// instance here; discharging every dispatch is the superset, so a dependency that
/// refuted, assumed or never verified a site is charged the same rows.
fn foreign_scan(tcx: TyCtxt<'_>, def: DefId) -> Option<ForeignScan> {
    if let Some(cached) = with_ledger(tcx.sess, |ledger| ledger.foreign_scans.get(&def).cloned()) {
        return cached;
    }
    let scan = foreign_site_scope(tcx, def).then(|| {
        let body = tcx.optimized_mir(def);
        let typing_env = ty::TypingEnv::post_analysis(tcx, def);
        let identity = ty::GenericArgs::identity_for_item(tcx, def);
        let mut direct = Vec::new();
        let mut edges = Vec::new();
        // Trust (OD-1 phase 2 review fix, 2026-10-05): what the body runs at an
        // instance that no site or edge below names. Each was silently dropped
        // before; the body's instances now discharge it `unknown`
        // ([`SiteKind::Opaque`]).
        let mut opaque: Vec<(Span, String)> = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                if let Some(why) = opaque_statement(tcx, body, statement) {
                    opaque.push((statement.source_info.span, why));
                }
            }
            let terminator = data.terminator();
            if let TerminatorKind::Drop { place, .. } = &terminator.kind {
                let dropped = place.ty(&body.local_decls, tcx).ty;
                if dropped.has_non_region_param() {
                    opaque.push((terminator.source_info.span, format!("drop glue of `{dropped}`")));
                }
                continue;
            }
            let (TerminatorKind::Call { func: callee, args: call_args, .. }
            | TerminatorKind::TailCall { func: callee, args: call_args, .. }) = &terminator.kind
            else {
                continue;
            };
            // A fn item at the body's parameters handed to the callee as a VALUE
            // (`x.map(Tr::m)`): whatever runs it is not this site.
            for arg in call_args.iter() {
                if let rustc_middle::mir::Operand::Constant(constant) = &arg.node
                    && let ty::FnDef(item, item_args) = *constant.const_.ty().peel_refs().kind()
                    && item_args.has_non_region_param()
                {
                    opaque.push((
                        constant.span,
                        format!(
                            "`{}` handed on as a value",
                            trust_mir_extract::safe_def_path_str_with_args(
                                tcx,
                                item,
                                item_args.skip_binder()
                            )
                        ),
                    ));
                }
            }
            if let Some(dispatch) = open_dispatch_at(tcx, body, typing_env, block) {
                if dispatch.own_params_only {
                    direct.push(SiteRecord {
                        block: block.as_u32(),
                        callee: dispatch.callee,
                        kind: if dispatch.through_pointer {
                            SiteKind::Pointer
                        } else {
                            SiteKind::Direct
                        },
                        span: terminator.source_info.span,
                        call_key: dispatch.dispatched,
                        accounted_key: None,
                    });
                } else {
                    opaque.push((
                        terminator.source_info.span,
                        format!(
                            "an open dispatch `{}` at arguments that are not its own parameters",
                            dispatch.dispatched
                        ),
                    ));
                }
                continue;
            }
            let Some((callee_def, args)) = callee.const_fn_def() else { continue };
            if !args.has_non_region_param() {
                continue;
            }
            let call_key = trust_mir_extract::func_operand_name_in_body(tcx, body, callee);
            let resolved = ty::Instance::try_resolve(tcx, typing_env, callee_def, args);
            let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args: item_args })) =
                resolved
            else {
                opaque.push((
                    terminator.source_info.span,
                    format!(
                        "a still-generic call to `{call_key}` that does not resolve to a body \
                         re-read here"
                    ),
                ));
                continue;
            };
            // Plain recursion at the identity arguments adds no instance; a
            // self-mention at other arguments (polymorphic recursion) is an edge, so
            // its discharge chain runs into the depth cap and fails closed.
            if item == def && item_args == identity {
                continue;
            }
            if !foreign_site_scope(tcx, item) {
                // Trust (OD-1 phase 2 review fix): an edge out of the declared scope
                // (a sysroot or undeclared crate, a crate the scope does not bind,
                // a closure body) was `continue`d here, so whatever it dispatches on
                // the parameters was charged nowhere.
                opaque.push((
                    terminator.source_info.span,
                    format!(
                        "a still-generic call to `{call_key}`, whose body is outside the \
                         declared scope"
                    ),
                ));
                continue;
            }
            edges.push(SiteRecord {
                block: block.as_u32(),
                callee: callee_def,
                kind: SiteKind::Via { callee: item, admitted: false },
                span: terminator.source_info.span,
                call_key,
                accounted_key: None,
            });
        }
        if let Some((span, first)) = opaque.first() {
            let more = opaque.len() - 1;
            let call_key = if more == 0 {
                format!("code not re-derived here: {first}")
            } else {
                format!("code not re-derived here: {first}, and {more} more")
            };
            direct.push(SiteRecord {
                block: OPAQUE_SITE_BLOCK,
                callee: def,
                kind: SiteKind::Opaque,
                span: *span,
                call_key,
                accounted_key: None,
            });
        }
        ForeignScan { direct, edges }
    });
    with_ledger(tcx.sess, |ledger| ledger.foreign_scans.insert(def, scan.clone()));
    scan
}

/// Trust (OD-1 phase 2 review fix, 2026-10-05): a statement of a dependency
/// generic body that hands a parameter-mentioning value to code no site names:
/// an unsizing coercion (`&X` to `&dyn Tr`: the vtable is the instance's), a
/// reification of a fn item or closure, or a fn item at the parameters used as a
/// value anywhere in the statement.
fn opaque_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    statement: &rustc_middle::mir::Statement<'tcx>,
) -> Option<String> {
    use rustc_middle::mir::{CastKind, Rvalue, StatementKind};
    use rustc_middle::ty::adjustment::PointerCoercion;
    let StatementKind::Assign(assign) = &statement.kind else { return None };
    let rvalue = &assign.1;
    if let Rvalue::Cast(
        CastKind::PointerCoercion(
            coercion @ (PointerCoercion::Unsize
            | PointerCoercion::ReifyFnPointer(_)
            | PointerCoercion::ClosureFnPointer(_)),
            _,
        ),
        operand,
        target,
    ) = rvalue
    {
        let source = operand.ty(&body.local_decls, tcx);
        if source.has_non_region_param() {
            return Some(match coercion {
                PointerCoercion::Unsize => format!("unsizing `{source}` to `{target}`"),
                _ => format!("reifying `{source}` to a fn pointer"),
            });
        }
    }
    struct FnValues<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: Option<String>,
    }
    impl<'tcx> Visitor<'tcx> for FnValues<'tcx> {
        fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _location: Location) {
            if self.found.is_none()
                && let ty::FnDef(item, args) = *constant.const_.ty().peel_refs().kind()
                && args.has_non_region_param()
            {
                self.found = Some(format!(
                    "`{}` used as a value",
                    trust_mir_extract::safe_def_path_str_with_args(
                        self.tcx,
                        item,
                        args.skip_binder()
                    )
                ));
            }
        }
    }
    let mut values = FnValues { tcx, found: None };
    values.visit_rvalue(rvalue, Location::START);
    values.found
}

/// Trust (OD-1 phase 2): does the dependency generic `def` reach an open-dispatch
/// site, itself or through its still-generic calls into other dependency generics?
/// A breadth-first walk over [`ForeignScan::edges`], so a cycle (mutual recursion)
/// is visited once and the answer does not depend on the order bodies are asked in.
/// Past [`FOREIGN_REACH_NODE_CAP`] bodies the answer is `true` (fail-closed).
fn foreign_reaches_site(tcx: TyCtxt<'_>, def: DefId) -> bool {
    if let Some(cached) = with_ledger(tcx.sess, |ledger| ledger.foreign_reaches.get(&def).copied())
    {
        return cached;
    }
    let mut seen: FxHashSet<DefId> = FxHashSet::default();
    let mut queue = std::collections::VecDeque::from([def]);
    let mut reaches = false;
    while let Some(next) = queue.pop_front() {
        if !seen.insert(next) {
            continue;
        }
        if seen.len() > FOREIGN_REACH_NODE_CAP {
            reaches = true;
            break;
        }
        let Some(scan) = foreign_scan(tcx, next) else { continue };
        if !scan.direct.is_empty() {
            reaches = true;
            break;
        }
        for edge in &scan.edges {
            if let SiteKind::Via { callee, .. } = edge.kind {
                queue.push_back(callee);
            }
        }
    }
    with_ledger(tcx.sess, |ledger| ledger.foreign_reaches.insert(def, reaches));
    reaches
}

/// Trust (OD-1 phase 2, 2026-10-05): the site records of the DEPENDENCY generic
/// `def`, re-derived in this compilation from its encoded MIR — its open dispatches
/// and the still-generic calls through which it reaches another dependency generic
/// that carries one. `None` when `def` is out of the declared scope
/// ([`foreign_site_scope`]). This is design §5's phase 2 through D4's channel: the
/// dependency exports nothing and is trusted for nothing (D4 rejected any rmeta
/// verdict bit); what it compiled is read, as D4-A/D4-B read it, and an instance
/// this compilation names is discharged against it exactly as a local carrier's is.
fn foreign_carrier_records(tcx: TyCtxt<'_>, def: DefId) -> Option<Vec<SiteRecord>> {
    let scan = foreign_scan(tcx, def)?;
    let mut records = scan.direct;
    for edge in scan.edges {
        if let SiteKind::Via { callee, .. } = edge.kind
            && foreign_reaches_site(tcx, callee)
        {
            records.push(edge);
        }
    }
    Some(records)
}

/// Trust (OD-1, 2026-10-04, open shapes): may the bridge lower the still-generic
/// call at `block` of the ROOT body `body` to the hypothesis-carrying local body
/// `carrier` UNDER the propagated hypotheses — havoc its result and the pointees it
/// can write, no absent-callee marker — instead of keeping its absent-callee row?
/// `Ok` carries the bridge's havoc argument indices.
///
/// Every conjunct is fail-closed (a refusal keeps the phase-1 row):
/// * the caller satisfies the body conjuncts of design §2.3 (`root_body_admits`),
///   so no safety invariant of the caller rests on what the callee does;
/// * the call owes no `requires` (`local_fn_item_owes_caller_precondition`): the
///   havoc charges no precondition;
/// * the carrier's OWN verdict passes the instance-RELATIVE evidence bar
///   (`trait_panic_free::InstanceRelative`): every safety row proved, no unproved
///   absent-callee/drop-glue row, no user axiom, no runtime-checked std member —
///   everything but its own instance hypotheses, which this body publishes as its
///   own rows (design §2.2: the substituted hypothesis joins `H_g`);
/// * the carrier trips no indirect-call gate of its own (that gate is a refusal,
///   not a row, so the bar cannot see it);
/// * every argument passes [`decide_arg`] (the one-level havoc covers what the
///   callee can write) and no other classification owns the call key.
fn via_call_admits<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    carrier: DefId,
    body_admitted: bool,
    decided_elsewhere: &impl Fn(&str) -> bool,
) -> Result<Vec<usize>, String> {
    if !body_admitted {
        return Err("the calling body fails the admission body conjuncts".to_string());
    }
    // Trust (OD-1 phase 2): a DEPENDENCY carrier's own relative verdict is not
    // re-derived here (only its sites are), so the call is never lowered under its
    // hypotheses: it keeps its absent-callee row, and the hypotheses travel as this
    // body's propagated rows only (phase 1's choice (7), kept for this case).
    if !carrier.is_local() {
        return Err("the callee is a dependency's generic body; its relative verdict is not \
                    re-derived here, so the call keeps its absent-callee row"
            .to_string());
    }
    let def = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, def);
    let (TerminatorKind::Call { func: callee, args, .. }
    | TerminatorKind::TailCall { func: callee, args, .. }) =
        &body.basic_blocks[block].terminator().kind
    else {
        return Err("not a call".to_string());
    };
    let Some((callee_def, callee_args)) = callee.const_fn_def() else {
        return Err("not a call to a fn item".to_string());
    };
    if decided_elsewhere(&trust_mir_extract::func_operand_name_in_body(tcx, body, callee)) {
        return Err("already classified elsewhere".to_string());
    }
    if super::local_fn_item_owes_caller_precondition(tcx, typing_env, callee_def, callee_args) {
        return Err("the callee owes its caller a `requires`".to_string());
    }
    if !tcx.is_mir_available(carrier) || super::optimized_mir_query_would_cycle(tcx, carrier) {
        return Err("the callee's MIR is unavailable or being computed up this stack".to_string());
    }
    super::trait_panic_free::instance_discharges_panic_freedom_modulo(
        tcx,
        ty::InstanceKind::Item(carrier),
        &super::trait_panic_free::InstanceRelative,
    )?;
    if super::function_has_unresolved_indirect_call(tcx, tcx.optimized_mir(carrier)) {
        return Err("the callee trips the indirect-call gate".to_string());
    }
    let decisions: Vec<ArgDecision> = args
        .iter()
        .map(|arg| decide_arg(&shape_of(tcx, typing_env, arg.node.ty(&body.local_decls, tcx))))
        .collect();
    site_admits(true, true, false, &decisions).map_err(str::to_string)
}

/// Record this ROOT body's admitted sites and its propagated ones, and return the
/// bridge's site set. Called at native-bundle construction, after every other
/// classification of the bundle is final, so `decided_elsewhere` sees the credited
/// rung-1/rung-2/D4-B keys.
///
/// The body is marked CONDITIONAL in the premise authenticator whenever it carries
/// any hypothesis, direct or propagated, so no premise lane spends its verdict.
pub(super) fn record_root_hypotheses<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &trust_types::VerifiableFunction,
    decided_elsewhere: impl Fn(&str) -> bool,
) -> trust_ir_bridge::InstanceHypothesisSites {
    let def = body.source.def_id();
    let admitted = admitted_sites(tcx, body, func, &decided_elsewhere);
    let mut bridge_sites = trust_ir_bridge::InstanceHypothesisSites::default();
    let mut records = Vec::new();
    // A pointer site's key (`TRUST_INDIRECT_CALLEE_PATH`) names every indirect call
    // of the body alike, so it is accounted for only when EVERY indirect call of the
    // body is an admitted pointer site.
    let indirect_calls = body
        .basic_blocks
        .iter()
        .filter(|data| {
            matches!(
                &data.terminator().kind,
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }
                    if func.const_fn_def().is_none()
            )
        })
        .count();
    let admitted_pointers = admitted.iter().filter(|site| site.through_pointer).count();
    for site in &admitted {
        if !bridge_sites.insert(
            &func.def_path,
            site.block.as_usize(),
            &site.call_key,
            site.havoc_args.clone(),
        ) {
            continue;
        }
        let terminator = body.basic_blocks[site.block].terminator();
        let accounted_key = (!site.through_pointer || admitted_pointers == indirect_calls)
            .then(|| site.call_key.clone());
        records.push(SiteRecord {
            block: site.block.as_u32(),
            callee: site.callee,
            kind: if site.through_pointer { SiteKind::Pointer } else { SiteKind::Direct },
            span: terminator.source_info.span,
            call_key: site.dispatched.clone(),
            accounted_key,
        });
    }
    // Propagation: a call that resolves to a local generic that carries hypotheses,
    // at arguments that still mention this body's parameters. The carrier test runs
    // on the RESOLVED body: a call names `<W<U> as Run>::run` (the trait item) while
    // the ledger holds the impl's method.
    let carriers = Carriers::snapshot(tcx.sess);
    let is_carrier = |item: DefId| carriers.contains(tcx, item);
    if body.source.promoted.is_none() {
        let typing_env = ty::TypingEnv::post_analysis(tcx, def);
        let body_admitted = root_body_admits(tcx, body, func);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let terminator = data.terminator();
            let (TerminatorKind::Call { func: callee, .. }
            | TerminatorKind::TailCall { func: callee, .. }) = &terminator.kind
            else {
                continue;
            };
            let Some((callee_def, args)) = callee.const_fn_def() else { continue };
            if !args.has_non_region_param() {
                continue;
            }
            let Some((carrier, _)) =
                resolved_carrier(tcx, typing_env, callee_def, args, &is_carrier)
            else {
                continue;
            };
            if carrier == def {
                continue;
            }
            let call_key = trust_mir_extract::func_operand_name_in_body(tcx, body, callee);
            let decision =
                via_call_admits(tcx, body, block, carrier, body_admitted, &decided_elsewhere);
            if super::env_flag_enabled("TRUST_INSTANCE_HYPOTHESIS_DEBUG") {
                eprintln!(
                    "[INSTANCE_HYPOTHESIS] {}: propagated call `{call_key}` at bb{}: {:?}",
                    func.def_path,
                    block.as_u32(),
                    decision
                );
            }
            let admitted = match decision {
                Ok(havoc_args) => {
                    bridge_sites.insert(&func.def_path, block.as_usize(), &call_key, havoc_args)
                }
                Err(_) => false,
            };
            records.push(SiteRecord {
                block: block.as_u32(),
                callee: callee_def,
                kind: SiteKind::Via { callee: carrier, admitted },
                span: terminator.source_info.span,
                accounted_key: admitted.then(|| call_key.clone()),
                call_key,
            });
        }
    }
    with_ledger(tcx.sess, |ledger| {
        if records.is_empty() {
            ledger.sites.remove(&def);
        } else {
            ledger.sites.insert(def, records.clone());
        }
    });
    if !records.is_empty() {
        super::record_instance_hypothesis_verdict(tcx.sess, def);
    }
    bridge_sites
}

/// The call keys of this body's calls the bridge lowered under a hypothesis (direct,
/// pointer and admitted propagated sites), which the zero-obligation transport
/// decision may treat as accounted for (by their hypothesis rows) when it asks
/// whether every call of a zero-obligation body was discharged. Never read by a
/// registry gate.
pub(super) fn admitted_site_call_keys(
    sess: &rustc_session::Session,
    def: DefId,
) -> FxHashSet<String> {
    with_ledger(sess, |ledger| {
        ledger
            .sites
            .get(&def)
            .map(|records| {
                records.iter().filter_map(|record| record.accounted_key.clone()).collect()
            })
            .unwrap_or_default()
    })
}

/// Trust (OD-1, 2026-10-04, open shapes): the MIR blocks of `def` whose call is an
/// admitted OPEN-DISPATCH site (direct or through a reified pointer), for the
/// indirect-call gate (`function_has_unresolved_indirect_call`): the dispatched
/// callee there is the published hypothesis, not an unresolved callable. A
/// propagated call is not one (its type arguments are asked as before).
pub(super) fn dispatch_site_blocks(sess: &rustc_session::Session, def: DefId) -> FxHashSet<u32> {
    with_ledger(sess, |ledger| {
        ledger
            .sites
            .get(&def)
            .map(|records| {
                records
                    .iter()
                    .filter(|record| matches!(record.kind, SiteKind::Direct | SiteKind::Pointer))
                    .map(|record| record.block)
                    .collect()
            })
            .unwrap_or_default()
    })
}

// ---------------------------------------------------------------------------
// Rows.
// ---------------------------------------------------------------------------

fn assumption_row(
    tag: &str,
    description: String,
    location: Option<SourceSpan>,
    reason: String,
) -> TransportObligationResult {
    TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: format!("assumption:{tag}"),
        original_vc_snapshot: None,
        typed_kind: None,
        description: format!("unverified assumption: {description}"),
        location,
        outcome: Outcome::Skipped,
        solver: INSTANCE_HYPOTHESIS_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(reason),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    }
}

/// The per-site definition row (also the propagated row, whose text says so).
fn hypothesis_row(
    func_path: &str,
    record: &SiteRecord,
    via: Option<&str>,
    location: Option<SourceSpan>,
) -> TransportObligationResult {
    let description = match (via, &record.kind) {
        (None, SiteKind::Pointer) => format!(
            "{INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX}call through a fn pointer reified from `{}` in \
             `{func_path}`: the panic-freedom of this open generic dispatch is assumed for every \
             instantiation; the obligation moves to each instance",
            record.call_key
        ),
        (None, _) => format!(
            "{INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX}call to `{}` in `{func_path}`: the panic-freedom \
             of this open generic dispatch is assumed for every instantiation; the obligation \
             moves to each instance",
            record.call_key
        ),
        (Some(inner), SiteKind::Via { admitted: true, .. }) => format!(
            "{INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX}call to `{}` in `{func_path}` carries the \
             callee's instance hypothesis `{inner}` (propagated; the instance is still generic \
             here; the callee's own rows prove the rest of its body relative to its hypotheses, \
             so the call is lowered under them)",
            record.call_key
        ),
        (Some(inner), _) => format!(
            "{INSTANCE_HYPOTHESIS_ASSUMPTION_PREFIX}call to `{}` in `{func_path}` carries the \
             callee's instance hypothesis `{inner}` (propagated; the instance is still generic \
             here)",
            record.call_key
        ),
    };
    assumption_row(
        INSTANCE_HYPOTHESIS_ASSUMPTION_TAG,
        description,
        location,
        format!(
            "instance hypothesis `{INSTANCE_HYPOTHESIS_ASSUMPTION_TAG}`: `{func_path}` claims \
             panic-freedom only under this premise (H(τ) ⇒ panic-free); a concrete instance is \
             charged by its discharge row; never proved, no credit; `--certify` refuses it"
        ),
    )
}

fn inventory_row() -> TransportObligationResult {
    assumption_row(
        INSTANCE_HYPOTHESIS_INVENTORY_INCOMPLETE_TAG,
        "instance inventory incomplete: discharge rows exist only for instances named in the \
         bodies this compilation verified or created by the vtables and drop glue those bodies \
         build; an instance created inside a dependency's generic code (a vtable it builds from \
         a type this crate hands it) or in an unwalked body has none"
            .to_string(),
        None,
        format!(
            "crate-level disclosure `{INSTANCE_HYPOTHESIS_INVENTORY_INCOMPLETE_TAG}`: the inventory \
             is not the codegen mono collector's; nothing is retired on its strength"
        ),
    )
}

fn discharge_row(
    description: String,
    location: Option<SourceSpan>,
    outcome: Outcome,
    reason: String,
) -> TransportObligationResult {
    TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        monitor: None,
        obligation_id: None,
        claim_digest_sha256: None,
        kind: INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND.to_string(),
        original_vc_snapshot: None,
        typed_kind: None,
        description,
        location,
        outcome,
        solver: INSTANCE_HYPOTHESIS_ROW_SOLVER.to_string(),
        time_ms: 0,
        counterexample: None,
        counterexample_model: None,
        reason: Some(reason),
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        grade: None,
    }
}

/// The hypothesis rows of one body: its direct sites, then its propagated ones
/// (one per site of the callee, substituted), then the crate's inventory row the
/// first time any body carries a hypothesis.
fn definition_rows<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Vec<TransportObligationResult> {
    let def = body.source.def_id();
    let Some(records) = with_ledger(tcx.sess, |ledger| ledger.sites.get(&def).cloned()) else {
        return Vec::new();
    };
    let mut rows = Vec::new();
    for record in &records {
        let location = Some(super::source_span_from_rustc_span(tcx, record.span));
        match &record.kind {
            SiteKind::Direct | SiteKind::Pointer | SiteKind::Opaque => {
                rows.push(hypothesis_row(func_path, record, None, location))
            }
            SiteKind::Via { callee, .. } => {
                let inner = carrier_records(tcx, *callee).unwrap_or_default();
                for site in &inner {
                    rows.push(hypothesis_row(
                        func_path,
                        record,
                        Some(&site.call_key),
                        location.clone(),
                    ));
                }
            }
        }
    }
    if !rows.is_empty() {
        let first = with_ledger(tcx.sess, |ledger| {
            !std::mem::replace(&mut ledger.inventory_row_published, true)
        });
        if first {
            rows.push(inventory_row());
        }
    }
    rows
}

/// The reason a discharge row carries when its carrier's site cannot be read back
/// without a query cycle ([`SiteReadback::Cycle`]).
const DISCHARGE_CYCLE_REASON: &str = "not established: the carrier's optimized MIR is not \
     computed yet and is on this query stack or in a mutual-recursion cycle with a body on it, \
     so its site cannot be read back at this instance without an E0391 query cycle; nothing \
     about the instance's callee was learned (this is no refutation), so the instance is not \
     established (an error on every fail-closed lane)";

/// Why a site of a carrier could not be read back at an instance.
enum SiteReadback {
    /// The carrier's `optimized_mir` is not computed yet and demanding it here could
    /// close a query cycle (it is on this stack, or a member of a mutual-recursion
    /// SCC with a body on it). Nothing about the instance was learned: the discharge
    /// is NOT ESTABLISHED (`unknown`), never `failed` — it is no evidence that the
    /// instance panics, and a `failed` row read as a refutation (regression
    /// `discharge-cycle`, 2026-10-05: four `failed` rows on ty's `cvw::all_same`,
    /// which `same_representation` calls and whose closure calls it back).
    Cycle,
    /// The recorded site no longer reads back as the call it was admitted on: the
    /// record and the body disagree, which fails closed.
    Mismatch(String),
}

/// The callee instance `site` reaches when its definition `def` runs at `args`
/// (concrete). `Err` with the reason when the site cannot be read back.
///
/// Trust (OD-1, 2026-10-05, regression `discharge-cycle`): a carrier the cycle
/// oracle declines is still read when its `optimized_mir` has already COMPLETED
/// ([`super::optimized_mir_if_completed`], a cache hit that runs no provider). The
/// oracle declines every member of a local mutual-recursion SCC outright, so before
/// this a mutually recursive carrier (`same_representation` ↔ `all_same`) could
/// never be discharged at any instance, even after its body was final.
fn substituted_site_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    site: &SiteRecord,
    args: GenericArgs<'tcx>,
) -> Result<(DefId, GenericArgs<'tcx>), SiteReadback> {
    let body = if super::optimized_mir_query_would_cycle(tcx, def) {
        super::optimized_mir_if_completed(tcx, def).ok_or(SiteReadback::Cycle)?
    } else {
        tcx.optimized_mir(def)
    };
    let mismatch = |why: &str| SiteReadback::Mismatch(why.to_string());
    let block = BasicBlock::from_u32(site.block);
    let Some(data) = body.basic_blocks.get(block) else {
        return Err(mismatch("the recorded site block is not in the definition's MIR"));
    };
    let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
        &data.terminator().kind
    else {
        return Err(mismatch("the recorded site is no longer a call"));
    };
    // A pointer site's item is read off the reification it was admitted on, with
    // the same structural pin (`reified_dispatch`).
    let named = match site.kind {
        SiteKind::Pointer => reified_dispatch(body, func).map(|(callee, args, _)| (callee, args)),
        SiteKind::Direct | SiteKind::Via { .. } => func.const_fn_def(),
        // Handled before any read-back (`discharge_instance`); never a call.
        SiteKind::Opaque => None,
    };
    let Some((callee, callee_args)) = named else {
        return Err(mismatch("the recorded site no longer names a fn item"));
    };
    if callee != site.callee {
        return Err(mismatch("the recorded site names a different callee"));
    }
    tcx.try_instantiate_and_normalize_erasing_regions(
        args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(tcx, callee_args),
    )
    .map(|substituted| (callee, substituted))
    .map_err(|_| mismatch("the substituted callee arguments do not normalize"))
}

/// Discharge every site of `def` at the concrete `args`, appending one row per
/// (site, interned instance) not yet published in this compilation.
fn discharge_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    def: DefId,
    args: GenericArgs<'tcx>,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    // Trust (regression `discharge-cycle`, review): a body that is no carrier still
    // owes its LATE cycle calls ([`discharge_late_cycle_calls`]) when it is a completed
    // generic in a local mutual-recursion cycle; for any other body this is empty.
    let records = carrier_records(tcx, def).unwrap_or_default();
    let instance_text = trust_mir_extract::safe_def_path_str_with_args(tcx, def, args);
    for record in &records {
        let key = (def, record.block, args.as_ptr() as usize);
        let first = with_ledger(tcx.sess, |ledger| ledger.published_discharges.insert(key));
        if !first {
            continue;
        }
        let location = Some(super::source_span_from_rustc_span(tcx, record.span));
        let mention_at = {
            let span = super::source_span_from_rustc_span(tcx, mention);
            // Trust (OD-1 phase 2): a dependency carrier's site was re-derived here
            // from its encoded MIR; the row says so, so it never reads as an import.
            if def.is_local() {
                format!("{}:{}", span.file, span.line_start)
            } else {
                format!(
                    "{}:{}; a site of a `{}` generic, re-derived from its encoded MIR",
                    span.file,
                    span.line_start,
                    tcx.crate_name(def.krate)
                )
            }
        };
        if let SiteKind::Opaque = record.kind {
            rows.push(discharge_row(
                format!(
                    "instance discharge: `{instance_text}` (named at {mention_at}) runs {}",
                    record.call_key
                ),
                location,
                Outcome::Unknown,
                "the dependency generic's body reaches code at this instance that its site \
                 inventory cannot see (a call out of the declared scope, a closure, drop glue, \
                 unsizing or reifying a parameter type, a fn item handed on as a value); nothing \
                 here establishes it, so the instance is not established (an error on every \
                 fail-closed lane)"
                    .to_string(),
            ));
            continue;
        }
        let (callee, callee_args) = match substituted_site_callee(tcx, def, record, args) {
            Ok(pair) => pair,
            Err(SiteReadback::Mismatch(why)) => {
                rows.push(discharge_row(
                    format!(
                        "instance discharge: site `{}` of `{instance_text}` (named at {mention_at})",
                        record.call_key
                    ),
                    location,
                    Outcome::Failed,
                    format!("unresolvable: {why}; an instance that cannot be resolved fails closed"),
                ));
                continue;
            }
            Err(SiteReadback::Cycle) => {
                rows.push(discharge_row(
                    format!(
                        "instance discharge: site `{}` of `{instance_text}` (named at {mention_at})",
                        record.call_key
                    ),
                    location,
                    Outcome::Unknown,
                    DISCHARGE_CYCLE_REASON.to_string(),
                ));
                continue;
            }
        };
        match &record.kind {
            SiteKind::Via { callee: carrier, .. } => {
                let carriers = Carriers::snapshot(tcx.sess);
                let resolved = resolved_carrier(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    callee,
                    callee_args,
                    &|item| carriers.contains(tcx, item),
                )
                .filter(|(item, _)| item == carrier);
                if depth >= DEPTH_CAP {
                    rows.push(discharge_row(
                        format!(
                            "instance discharge: site `{}` of `{instance_text}` (named at {mention_at})",
                            record.call_key
                        ),
                        location,
                        Outcome::Failed,
                        "the propagation chain exceeds its depth cap; failed closed".to_string(),
                    ));
                } else if let Some((item, item_args)) = resolved {
                    discharge_instance(tcx, root, item, item_args, mention, depth + 1, rows);
                } else {
                    rows.push(discharge_row(
                        format!(
                            "instance discharge: site `{}` of `{instance_text}` (named at {mention_at})",
                            record.call_key
                        ),
                        location,
                        Outcome::Failed,
                        "the propagated call does not resolve, at this instance, to the body whose \
                         hypotheses it carries; failed closed"
                            .to_string(),
                    ));
                }
            }
            SiteKind::Direct | SiteKind::Pointer => {
                let resolved = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    callee,
                    callee_args,
                );
                let callee_text =
                    trust_mir_extract::safe_def_path_str_with_args(tcx, callee, callee_args);
                let description = format!(
                    "instance discharge: site `{}` of `{instance_text}` (named at {mention_at}) \
                     resolves to `{callee_text}`",
                    record.call_key
                );
                // Trust (OD-1 phase 2 review fix): a resolved DEPENDENCY callee
                // that carries open dispatch of its own propagates: its sites are
                // discharged at its instance, after this row.
                let mut propagate = None;
                let (outcome, reason) = match resolved {
                    Ok(Some(instance)) => match instance.def {
                        ty::InstanceKind::Virtual(..) => (
                            Outcome::Failed,
                            "a virtual call; phase 1 consults no `dyn` lane for a discharge, so it \
                             fails closed"
                                .to_string(),
                        ),
                        kind if kind.def_id().is_local() => {
                            match super::trait_panic_free::instance_discharges_panic_freedom(tcx, kind) {
                                Ok(()) => (
                                    Outcome::Proved,
                                    "the resolved callee's own body discharges panic-freedom on the \
                                     shared evidence bar; its own rows carry the proof, this row \
                                     carries no credit"
                                        .to_string(),
                                ),
                                Err(why) => local_callee_refusal(tcx, kind, why),
                            }
                        }
                        // Trust (OD-1 phase 2): a resolved callee in a DEPENDENCY. Nothing
                        // the dependency concluded is read (D4); what this row may say
                        // depends on what THIS compilation knows about the body:
                        ty::InstanceKind::Item(item) => {
                            dependency_callee_discharge(tcx, instance, item, root, depth, &mut propagate)
                        }
                        // Not `runtime_checked`: every non-proved discharge is an error on
                        // the fail-closed lanes (`report_unestablished_discharges`), and a
                        // published `runtime_checked` would read as a verdict strict
                        // tolerates. Nothing in this compilation established the callee.
                        _ => (
                            Outcome::Unknown,
                            "the resolved callee's body is outside this crate and is not bundled; \
                             this compilation has no verdict for it, so the instance is not \
                             established (an error on every fail-closed lane)"
                                .to_string(),
                        ),
                    },
                    Ok(None) => (
                        Outcome::Failed,
                        "unresolvable under a fully monomorphized typing environment; failed closed"
                            .to_string(),
                    ),
                    Err(_) => (
                        Outcome::Failed,
                        "resolution reported an error; failed closed".to_string(),
                    ),
                };
                rows.push(discharge_row(description, location, outcome, reason));
                if let Some((item, item_args)) = propagate {
                    discharge_instance(tcx, root, item, item_args, mention, depth + 1, rows);
                }
            }
            // Handled at the top of the loop.
            SiteKind::Opaque => {}
        }
    }
    discharge_late_cycle_calls(tcx, root, def, args, mention, depth, rows);
    // Trust (OD-1 item 19, vtable-only discharge): the vtables and drop glue this
    // local generic body builds at this instance, and the local generics it calls on.
    glue::discharge_glue_of_instance(tcx, root, def, args, mention, depth, rows);
}

/// Trust (OD-1, 2026-10-06, regression `discharge-cycle`, review defect 1): the calls
/// of a COMPLETED local generic `def` in a mutual-recursion cycle into a sibling
/// generic of that cycle that its ledger records do not cover, discharged at the
/// concrete `args`.
///
/// The ledger is filled in verification order. Inside a mutual-recursion SCC a member
/// can be verified before a sibling generic it calls at its own parameters; the
/// sibling's sites are not recorded yet, so the carrier test said "no" and `def` got
/// no [`SiteKind::Via`] record for the call — whatever the sibling turns out to
/// carry. Measured: `inner<T>` → `inner2<T>` (dispatches `t.m()`, calls `outer`) →
/// `outer` → `inner(&Bad, ..)`, verified `inner`, `outer`, `inner2`: no discharge row
/// for `inner2::<Bad>` at all, and none for `inner::<Bad>` named by a `top` outside
/// the cycle.
///
/// `def`'s body is final once its `optimized_mir` completed (`TrustVerify` is that
/// pipeline's last pass), so the call is re-read from it here, at discharge time, and
/// each uncovered sibling instance is decided by what is known NOW:
/// * a sibling that is a carrier by now: discharged at its instance, like a `Via`
///   record (its refutation is a `failed` row, its proof a `proved` row with no credit);
/// * a sibling still not verified: the `unknown` row of [`unverified_cycle_generic_row`];
/// * a verified sibling that carries nothing: recursed into, for ITS late calls.
///
/// A `def` that is not a local generic in a cycle, or not completed, has none (a
/// body outside every cycle is verified after its callees, so its records are
/// complete; an uncompleted one is the caller's [`unverified_cycle_generic`] case).
fn discharge_late_cycle_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    def: DefId,
    args: GenericArgs<'tcx>,
    mention: Span,
    depth: u32,
    rows: &mut Vec<TransportObligationResult>,
) {
    if !is_local_cycle_generic(tcx, def) {
        return;
    }
    let Some(body) = super::optimized_mir_if_completed(tcx, def) else {
        return;
    };
    let covered: FxHashSet<u32> = with_ledger(tcx.sess, |ledger| {
        ledger
            .sites
            .get(&def)
            .map(|records| {
                records
                    .iter()
                    .filter(|record| matches!(record.kind, SiteKind::Via { .. }))
                    .map(|record| record.block)
                    .collect()
            })
            .unwrap_or_default()
    });
    let generic_env = ty::TypingEnv::post_analysis(tcx, def);
    let mono_env = ty::TypingEnv::fully_monomorphized();
    let instance_text = trust_mir_extract::safe_def_path_str_with_args(tcx, def, args);
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let terminator = data.terminator();
        let (TerminatorKind::Call { func: callee, .. }
        | TerminatorKind::TailCall { func: callee, .. }) = &terminator.kind
        else {
            continue;
        };
        let Some((callee_def, callee_args)) = callee.const_fn_def() else { continue };
        if !callee_args.has_non_region_param() || covered.contains(&block.as_u32()) {
            continue;
        }
        // The sibling, as the call resolves in `def`'s own typing environment (the
        // carrier test of `record_root_hypotheses` runs on exactly this).
        let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(sibling), .. })) =
            ty::Instance::try_resolve(tcx, generic_env, callee_def, callee_args)
        else {
            continue;
        };
        if sibling == def || !is_local_cycle_generic(tcx, sibling) {
            continue;
        }
        let key = (def, block.as_u32(), args.as_ptr() as usize);
        if !with_ledger(tcx.sess, |ledger| ledger.published_discharges.insert(key)) {
            continue;
        }
        let call_key = trust_mir_extract::func_operand_name_in_body(tcx, body, callee);
        let location = Some(super::source_span_from_rustc_span(tcx, terminator.source_info.span));
        let unestablished = |outcome: Outcome, why: &str| {
            let mention_at = super::source_span_from_rustc_span(tcx, mention);
            discharge_row(
                format!(
                    "instance discharge: cycle call `{call_key}` of `{instance_text}` (named at                      {}:{})",
                    mention_at.file, mention_at.line_start
                ),
                location.clone(),
                outcome,
                why.to_string(),
            )
        };
        if depth >= DEPTH_CAP {
            rows.push(unestablished(
                Outcome::Failed,
                "the propagation chain exceeds its depth cap; failed closed",
            ));
            continue;
        }
        let resolved = tcx
            .try_instantiate_and_normalize_erasing_regions(
                args,
                mono_env,
                ty::EarlyBinder::bind(tcx, callee_args),
            )
            .ok()
            .and_then(|substituted| {
                match ty::Instance::try_resolve(tcx, mono_env, callee_def, substituted) {
                    Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) => {
                        Some((item, args))
                    }
                    _ => None,
                }
            });
        let Some((item, item_args)) = resolved else {
            rows.push(unestablished(
                Outcome::Failed,
                "unresolvable: the call into a generic of this mutual-recursion cycle does not                  resolve to a body at this instance; an instance that cannot be resolved fails                  closed",
            ));
            continue;
        };
        if carrier_records(tcx, item).is_none()
            && super::optimized_mir_if_completed(tcx, item).is_none()
        {
            unverified_cycle_generic_row(tcx, item, item_args, mention, rows);
        } else {
            discharge_instance(tcx, root, item, item_args, mention, depth + 1, rows);
        }
    }
}

/// A local plain generic `fn` item in a local mutual-recursion cycle (or on this
/// query stack): the bodies whose ledger records can miss a sibling verified later.
fn is_local_cycle_generic(tcx: TyCtxt<'_>, def: DefId) -> bool {
    def.is_local()
        && matches!(tcx.def_kind(def), DefKind::Fn | DefKind::AssocFn)
        && tcx.generics_of(def).requires_monomorphization(tcx)
        && super::optimized_mir_query_would_cycle(tcx, def)
}

/// Trust (2026-10-19, DISCHARGE-NO-EVIDENCE-1): the verdict of a discharge whose
/// resolved LOCAL callee `kind` the shared evidence bar refused with `why`. `failed`
/// only when the callee's own ledger carries evidence it can panic; a refusal that
/// rests on absent callees and unmodeled MIR alone
/// (`trait_panic_free::refusal_carries_no_violation_evidence`) is the callee's own
/// `unknown`, carried as `unknown` (design §2.2: the row takes the callee instance's
/// existing verdict). Before, every refusal was `failed` under the bare
/// `trust-classifier` solver, which reads `refuted`, and the `--allow-l0-gaps` gate
/// failed on callees whose own rows it tolerated (measured on aterm's
/// `LaunchApply::runs::<{closure}>`, Trust 0.11.0 cut `20565c3255a`) — the same
/// misreading item 2 of [`dependency_callee_discharge`] removed for propagating
/// dependency callees. Both outcomes are errors on every fail-closed lane.
fn local_callee_refusal<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: ty::InstanceKind<'tcx>,
    why: String,
) -> (Outcome, String) {
    if super::trait_panic_free::refusal_carries_no_violation_evidence(tcx, kind) {
        (
            Outcome::Unknown,
            format!(
                "the resolved callee is not proved panic-free: {why}; nothing in its own ledger \
                 is evidence that it panics (each unproved row is an absent callee or unmodeled \
                 MIR, with no refuted, held or policy-refuted row, and its one admitted premise \
                 is an unsafe block declared on its SAFETY comment), so the instance is not \
                 established (an error on every fail-closed lane), not refuted"
            ),
        )
    } else {
        (Outcome::Failed, format!("the resolved callee is not proved panic-free: {why}"))
    }
}

/// Trust (OD-1 phase 2; review fixes 2026-10-05): the verdict of one discharge
/// whose resolved callee `instance` is the DEPENDENCY body `item`. In order:
///
/// 1. a SOUNDNESS decline of D4-A (undeclared, sysroot, interposable symbol, user
///    `unsafe`, an inlined `requires` callee, ...) is `unknown` and names that
///    conjunct — this compilation may not read a verdict for the body at all;
/// 2. a callee that is itself a dependency generic carrying sites (a default
///    method dispatching on `Self`, `ExprFold::fold_box`) PROPAGATES: `unknown`
///    here (its instance-relative verdict is not re-derived), and its own sites
///    are discharged at its instance (`propagate`, below the depth cap) — it was a
///    `failed` row that read as a refutation;
/// 3. a callee this compilation has NOT already re-derived for a credit-bearing
///    check is `unknown`: a discharge carries no credit, so it never spends the
///    shared D4-A budget (`foreign_rederivation_already_admitted`); spending it
///    here took the budget a later `dyn` case split needed (measured with
///    `TRUST_REDERIVE_MAX_BODIES=1`: C-FLOW declined, the `dyn` site kept);
/// 4. otherwise the shared bar over the verdict computed HERE
///    (`dyn_target_is_verified_panic_free`, which charges nothing new for an
///    admitted body): `proved` (no credit) or `failed`.
fn dependency_callee_discharge<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    item: DefId,
    root: DefId,
    depth: u32,
    propagate: &mut Option<(DefId, GenericArgs<'tcx>)>,
) -> (Outcome, String) {
    use super::foreign_rederivation as fr;
    const NOT_ESTABLISHED: &str = "this compilation has no verdict for it, so the instance is \
                                   not established (an error on every fail-closed lane)";
    if let Some(decline) = fr::foreign_rederivation_soundness_decline(tcx, item) {
        return (
            Outcome::Unknown,
            format!("the resolved callee is a body that {}; {NOT_ESTABLISHED}", decline.reason()),
        );
    }
    if carrier_records(tcx, item).is_some() {
        if depth + 1 >= DEPTH_CAP {
            return (
                Outcome::Failed,
                "the resolved callee is a dependency generic with open dispatch of its own, and \
                 the propagation chain exceeds its depth cap; failed closed"
                    .to_string(),
            );
        }
        *propagate = Some((item, instance.args));
        return (
            Outcome::Unknown,
            format!(
                "the resolved callee is a dependency generic body with open dispatch of its own: \
                 its verdict is only RELATIVE to its own sites, which are discharged at this \
                 instance by the rows that follow; its relative verdict is not re-derived here, \
                 so {NOT_ESTABLISHED}"
            ),
        );
    }
    if let Some(decline) = fr::peek_foreign_rederivation(tcx, item) {
        return (
            Outcome::Unknown,
            format!(
                "the resolved callee is a dependency body that {}; {NOT_ESTABLISHED}",
                decline.reason()
            ),
        );
    }
    if !fr::foreign_rederivation_already_admitted(tcx, item) {
        return (
            Outcome::Unknown,
            format!(
                "the resolved callee is a dependency body no credit-bearing check of this \
                 compilation has re-derived (so far); a discharge carries no credit and does not \
                 spend the shared re-derivation budget, so {NOT_ESTABLISHED}"
            ),
        );
    }
    if super::dyn_dispatch_reliance::dyn_target_is_verified_panic_free(tcx, instance, root) {
        (
            Outcome::Proved,
            "the resolved callee is a dependency body RE-DERIVED in this compilation (D4-A) and \
             discharges panic-freedom on the shared evidence bar; its re-derived rows carry the \
             proof, this row carries no credit"
                .to_string(),
        )
    } else {
        (
            Outcome::Failed,
            "the resolved callee is a dependency body RE-DERIVED in this compilation (D4-A), and \
             it does not discharge panic-freedom on the shared evidence bar (its re-derived \
             verdict, or a pre-conjunct: a `#[trust::skip]`/`assume_total` body, an authored \
             clause, a cycle); failed closed"
                .to_string(),
        )
    }
}

/// The discharge rows a body owes: one per (site, concrete instance) of every
/// hypothesis-carrying local generic it names at concrete arguments, not yet
/// published by an earlier body. The carrier test runs on the RESOLVED instance
/// ([`resolved_carrier`]): `<W<[u8; 3]> as Run>::run` names the trait item, and is an
/// instance of the impl's method, which is what carries the hypothesis; an impl that
/// overrides a trait default method resolves to the override, never to the default
/// body. A mention of the body itself at concrete arguments is not skipped: its
/// discharge would read the body's own MIR, which is being computed, so the row is
/// `unknown` (not established; [`SiteReadback::Cycle`]) and an error on every
/// fail-closed lane.
fn discharge_rows<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<TransportObligationResult> {
    let carriers = Carriers::snapshot(tcx.sess);
    let is_carrier = |item: DefId| carriers.contains(tcx, item);
    let root = body.source.def_id();
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let mut foreign_discharged = false;
    let mut rows = Vec::new();
    for (def, args, span) in fn_item_mentions(tcx, body) {
        if args.has_non_region_param() {
            continue;
        }
        let Ok(args) = tcx.try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::Unnormalized::new_wip(args),
        ) else {
            continue;
        };
        if let Some((item, item_args)) = resolved_carrier(tcx, typing_env, def, args, &is_carrier) {
            let before = rows.len();
            discharge_instance(tcx, root, item, item_args, span, 0, &mut rows);
            foreign_discharged |= !item.is_local() && rows.len() > before;
        } else if let Some((item, item_args)) =
            unverified_cycle_generic(tcx, typing_env, root, def, args)
        {
            unverified_cycle_generic_row(tcx, item, item_args, span, &mut rows);
        } else if let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) =
            ty::Instance::try_resolve(tcx, typing_env, def, args)
            && item.is_local()
            && item != root
        {
            // Trust (OD-1 item 20, T6, 2026-10-10): a concrete call of a local CLOSURE
            // (`<{closure} as Fn<A>>::call`, the closure returned by a generic `make::<τ>`)
            // whose body is not verified yet: its admitted sites are not recorded, so the
            // carrier test above said "no". It is verified first when that is safe, and is
            // an `unknown` row otherwise (`glue::discharge_reached`), never skipped.
            if tcx.is_closure_like(item) {
                glue::discharge_reached(
                    tcx,
                    root,
                    item,
                    args,
                    "a call of the closure",
                    span,
                    0,
                    &mut rows,
                );
                continue;
            }
            // A verified generic of a cycle that carries nothing (yet) can still reach
            // a sibling verified after it ([`discharge_late_cycle_calls`]); for any
            // other body this publishes nothing.
            discharge_instance(tcx, root, item, args, span, 0, &mut rows);
        }
    }
    // Trust (OD-1 item 19, vtable-only discharge): an instance no body names but a
    // vtable or drop glue of this body creates (`&W(Bad) as &dyn Run`, `drop(W(Bad))`)
    // is charged like a named one, off the body's recorded mentioned items (the set
    // the codegen collector reads, kept across inlining); a value handed to a
    // dependency generic is charged its drop glue there (`glue`).
    let mentioned = glue::mentions(tcx, body);
    for (glue_item, span) in mentioned.glue {
        if !glue_item.has_non_region_param() {
            glue::discharge_glue(tcx, root, glue_item, span, 0, &mut rows);
        }
    }
    for (def, args, span) in mentioned.items {
        if args.has_non_region_param() || tcx.is_closure_like(def) {
            continue;
        }
        let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) =
            ty::Instance::try_resolve(tcx, typing_env, def, args)
        else {
            continue;
        };
        if !tcx.generics_of(item).requires_monomorphization(tcx) {
            continue;
        }
        if item.is_local() {
            // A local generic the MIR inliner removed from the optimized body is still
            // a recorded mention: its vtables and drop glue are charged at this
            // instance (once per instance; a no-op when the loop above reached it).
            glue::discharge_glue_of_instance(tcx, root, item, args, span, 0, &mut rows);
        } else {
            glue::discharge_dependency_call_drops(tcx, root, args, span, 0, &mut rows);
        }
    }
    // Trust (OD-1 phase 2): discharges of a dependency generic's instances are read off
    // this compilation's own mentions, never the codegen mono collector's inventory,
    // so the crate's inventory-incomplete disclosure is owed here too (once).
    if foreign_discharged {
        let first = with_ledger(tcx.sess, |ledger| {
            !std::mem::replace(&mut ledger.inventory_row_published, true)
        });
        if first {
            rows.push(inventory_row());
        }
    }
    rows
}

/// Trust (OD-1, 2026-10-05, regression `discharge-cycle`): the LOCAL generic body a
/// concrete mention resolves to when the carrier test cannot answer for it yet. The
/// ledger is filled in verification order, and the callee-first demand order puts a
/// callee first everywhere except inside a mutual-recursion SCC, where some member is
/// verified before a sibling it names. When that sibling is generic, its admitted
/// sites are not recorded yet, so the carrier test says "no" for a body that may
/// carry hypotheses — and the instance was silently never discharged (measured on a
/// two-function SCC, `fn inner<T: Tr>` declared before `pub fn outer`, which calls
/// `inner(&Good, ..)`: no discharge row at all). It cannot be verified from here
/// either: the cycle oracle declines its `optimized_mir`, and only a completed one
/// (a cache hit) settles the question.
///
/// `Some` exactly when the mention resolves to a local plain generic `fn` item other
/// than `root` (asked only after [`resolved_carrier`] found no carrier), whose
/// `optimized_mir` the cycle oracle declines and has not completed. A completed body
/// was verified, so its absence from the ledger says its OWN sites are none — but not
/// that it reaches none: it may call a sibling generic of the cycle verified after it,
/// which [`discharge_late_cycle_calls`] re-reads from its completed body.
fn unverified_cycle_generic<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    root: DefId,
    def: DefId,
    args: GenericArgs<'tcx>,
) -> Option<(DefId, GenericArgs<'tcx>)> {
    let Ok(Some(ty::Instance { def: ty::InstanceKind::Item(item), args })) =
        ty::Instance::try_resolve(tcx, typing_env, def, args)
    else {
        return None;
    };
    let pending = item.is_local()
        && item != root
        && matches!(tcx.def_kind(item), DefKind::Fn | DefKind::AssocFn)
        && tcx.generics_of(item).requires_monomorphization(tcx)
        && super::optimized_mir_query_would_cycle(tcx, item)
        && super::optimized_mir_if_completed(tcx, item).is_none();
    pending.then_some((item, args))
}

/// The `unknown` discharge row of an [`unverified_cycle_generic`] instance, once per
/// interned instance in this compilation.
fn unverified_cycle_generic_row<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: DefId,
    args: GenericArgs<'tcx>,
    mention: Span,
    rows: &mut Vec<TransportObligationResult>,
) {
    let key = (item, UNVERIFIED_CYCLE_GENERIC_BLOCK, args.as_ptr() as usize);
    if !with_ledger(tcx.sess, |ledger| ledger.published_discharges.insert(key)) {
        return;
    }
    let instance_text = trust_mir_extract::safe_def_path_str_with_args(tcx, item, args);
    let mention_at = super::source_span_from_rustc_span(tcx, mention);
    rows.push(discharge_row(
        format!(
            "instance discharge: `{instance_text}` (named at {}:{}) is a generic body in a \
             mutual-recursion cycle with this one that is not verified yet",
            mention_at.file, mention_at.line_start
        ),
        Some(mention_at),
        Outcome::Unknown,
        "not established: the named generic is verified after this body (they call each \
         other, so the callee-first order cannot put it first) and its optimized MIR cannot \
         be demanded here without an E0391 query cycle, so whether it carries instance \
         hypotheses — and whether this instance discharges them — is unknown here; the \
         instance is not established (an error on every fail-closed lane)"
            .to_string(),
    ));
}

/// Every instance-hypothesis row `body` publishes: definition rows (direct and
/// propagated), the crate's inventory row the first time, and the discharge rows
/// of the instances it names.
pub(super) struct InstanceHypothesisCharge {
    pub(super) rows: Vec<TransportObligationResult>,
}

impl InstanceHypothesisCharge {
    /// The per-site hypothesis rows (direct and propagated), not the inventory row.
    fn hypotheses(&self) -> impl Iterator<Item = &TransportObligationResult> {
        let kind = format!("assumption:{INSTANCE_HYPOTHESIS_ASSUMPTION_TAG}");
        self.rows.iter().filter(move |row| {
            row.kind == kind && is_instance_hypothesis_assumption_row(&row.kind, &row.solver)
        })
    }

    /// Discharge rows that did not establish the instance (anything but `proved`).
    fn unestablished_discharges(&self) -> impl Iterator<Item = &TransportObligationResult> {
        self.rows.iter().filter(|row| {
            is_instance_hypothesis_discharge_row(&row.kind, &row.solver)
                && row.outcome != Outcome::Proved
        })
    }

    pub(super) fn has_hypotheses(&self) -> bool {
        self.hypotheses().next().is_some()
    }

    /// Whether this charge publishes at least one hypothesis row and every one has
    /// the exact compiler shape ([`transport_row_is_instance_hypothesis_assumption`]).
    /// The zero-obligation transport decision lets the hypothesis rows account for
    /// a body's admitted calls only on this answer: a row of any other shape is no
    /// disclosure, and the honest gap row is owed.
    pub(super) fn hypotheses_are_exact(&self) -> bool {
        self.has_hypotheses()
            && self.hypotheses().all(transport_row_is_instance_hypothesis_assumption)
    }
}

pub(super) fn instance_hypothesis_charge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Option<InstanceHypothesisCharge> {
    if body.source.promoted.is_some() {
        return None;
    }
    let mut rows = definition_rows(tcx, body, func_path);
    rows.extend(discharge_rows(tcx, body));
    (!rows.is_empty()).then_some(InstanceHypothesisCharge { rows })
}

/// Whether a published row has one of this module's exact shapes (any outcome).
fn is_own_row(row: &TransportObligationResult) -> bool {
    is_instance_hypothesis_assumption_row(&row.kind, &row.solver)
        || is_instance_hypothesis_discharge_row(&row.kind, &row.solver)
        || row.kind.starts_with(&format!("assumption:{INSTANCE_HYPOTHESIS_ASSUMPTION_TAG}"))
        || row.kind == INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND
}

/// `rows` with every pre-existing row claiming one of this module's kinds removed
/// (staleness/forgery defence, as the D9 seam does) and the charge appended. `None`
/// when there is nothing to strip or append.
pub(super) fn rows_with_instance_hypotheses(
    rows: &[TransportObligationResult],
    charge: Option<&InstanceHypothesisCharge>,
) -> Option<Vec<TransportObligationResult>> {
    if charge.is_none() && !rows.iter().any(is_own_row) {
        return None;
    }
    let mut out: Vec<TransportObligationResult> =
        rows.iter().filter(|row| !is_own_row(row)).cloned().collect();
    if let Some(charge) = charge {
        out.extend(charge.rows.iter().cloned());
    }
    Some(out)
}

/// The exact compiler shape of the definition/inventory rows, for the zero-obligation
/// transport decision ([`InstanceHypothesisCharge::hypotheses_are_exact`]).
pub(super) fn transport_row_is_instance_hypothesis_assumption(
    row: &TransportObligationResult,
) -> bool {
    is_instance_hypothesis_assumption_row(&row.kind, &row.solver)
        && row.outcome == Outcome::Skipped
        && row.typed_kind.is_none()
        && !row.design_mandate
        && row.native_trust_ir.is_none()
        && row.proof_evidence.is_none()
}

// ---------------------------------------------------------------------------
// Diagnostics.
// ---------------------------------------------------------------------------

const DISCLOSURE_NOTE: &str = "recorded as `assumption:instance-hypothesis` (skipped, NOT proved): \
     the crate's result is CONDITIONAL on every instance's callee being panic-free, each concrete \
     instance this compilation names is charged by an `instance-hypothesis:discharge` row, and \
     `-Ztrust-policy=certify` refuses it";

/// The human disclosure on every non-`certify` lane.
pub(super) fn warn_instance_hypotheses(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
) {
    if let Some(prepared) = prepare_instance_hypothesis_warning(tcx, body, func_path, charge) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_instance_hypothesis_warning(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
) -> Option<PreparedLocatedDiagnostic> {
    let count = charge.hypotheses().count();
    if count == 0 {
        return None;
    }
    Some(PreparedLocatedDiagnostic {
        span: tcx.def_span(body.source.def_id()),
        diagnostic: PreparedDiagnostic {
            aborting: false,
            header: format!(
                "Trust verification advisory for `{func_path}`: {count} instance hypothesis row(s) — \
                 panic-freedom of open generic dispatch is ASSUMED per instance, not proved"
            ),
            children: vec![PreparedDiagnosticChild::Note(DISCLOSURE_NOTE.into())],
        },
    })
}

/// A discharge row that did not establish its instance is an error on every
/// fail-closed lane (strict, certify) and a warning under advisory: the instance
/// this compilation itself creates may panic.
pub(super) fn report_unestablished_discharges(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
    fail_closed: bool,
) {
    if let Some(prepared) = prepare_unestablished_discharges(
        tcx, body, func_path, charge, fail_closed,
    ) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_unestablished_discharges(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
    fail_closed: bool,
) -> Option<PreparedLocatedDiagnostic> {
    let unestablished: Vec<&TransportObligationResult> =
        charge.unestablished_discharges().collect();
    if unestablished.is_empty() {
        return None;
    }
    let message = format!(
        "Trust instance discharge not established for `{func_path}`: {} instance(s) named here \
         reach a callee whose panic-freedom is not proved",
        unestablished.len()
    );
    let notes: Vec<String> = unestablished
        .iter()
        .map(|row| format!("{} [{}]", row.description, row.outcome.as_str()))
        .collect();
    let span = tcx.def_span(body.source.def_id());
    Some(PreparedLocatedDiagnostic {
        span,
        diagnostic: PreparedDiagnostic {
            aborting: fail_closed,
            header: message,
            children: notes.into_iter().map(PreparedDiagnosticChild::Note).collect(),
        },
    })
}

/// `certify` refuses a function that carries an instance hypothesis.
pub(super) fn abort_on_instance_hypotheses(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
) {
    if let Some(prepared) = prepare_instance_hypothesis_refusal(tcx, body, func_path, charge) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_instance_hypothesis_refusal(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    func_path: &str,
    charge: &InstanceHypothesisCharge,
) -> Option<PreparedLocatedDiagnostic> {
    let count = charge.hypotheses().count();
    if count == 0 {
        return None;
    }
    Some(PreparedLocatedDiagnostic {
        span: tcx.def_span(body.source.def_id()),
        diagnostic: PreparedDiagnostic {
            aborting: true,
            header: format!(
                "Trust certify verification failed for `{func_path}`: {count} instance hypothesis \
                 row(s) — panic-freedom of open generic dispatch is assumed, not proved"
            ),
            children: vec![PreparedDiagnosticChild::Note(
                "under `-Ztrust-policy=certify` an `assumption:instance-hypothesis` row is fatal; the \
                 default lane records it and passes CONDITIONALLY".into(),
            )],
        },
    })
}

// Trust (2026-10-10, CALL-REACH-1 D2): visible to `sysroot_drop_reach`, whose call
// walk reads `glue::unsize_tails` for the vtables a walked body builds.
pub(in crate::trust_verify) mod glue;

#[cfg(test)]
mod tests;
