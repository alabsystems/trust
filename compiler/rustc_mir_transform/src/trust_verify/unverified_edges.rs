//! Trust (r15, 2026-10-01): the ONE enumeration of the edges out of a MIR body into
//! code this compilation does not verify.
//!
//! An assumption row that stands for a body nothing verified is admissible only
//! when every way that body can run code it does not own is either charged or
//! absent. Two such rows asked this question with two separate scans, and each
//! scan knew a different subset of the edges:
//!
//! * the memory-safe skip/collapse rows (`memory_safe_assumption_uncharged_edges`)
//!   looked at `Call`, `TailCall` and `Drop` terminators only, so a READ of a
//!   local `safe static` from an `unsafe extern` block was no edge. MEASURED on
//!   stage-1 `ae0494648a`, `-Ztrust-policy=memory-safe`: `fn skipped(s: &S) -> u32
//!   { let _q = &raw const s.a; *TRUST_R }` (classifier-skipped as
//!   `addr-of-field`) built rc=0 with an `assumption:addr-of-field` row, and the
//!   binary died with SIGSEGV (139) dereferencing the NULL the symbol held;
//! * the `#[trust::assume_total]` revocation (`assume_total_cannot_cover_body`)
//!   looked at user `unsafe`, local foreign-item calls, foreign statics and
//!   validity transmutes, so a call into a verify-off DEPENDENCY's safe fn was no
//!   edge. MEASURED on the same compiler: `#[trust::assume_total] fn t(x: u32) ->
//!   u32 { dep::null_fn(); x }` built rc=0 in the default, strict AND memory-safe
//!   lanes and every binary died with SIGSEGV; a memory-safe skip body calling `t`
//!   was admitted too (`local_item_is_held_to_this_rule` accepts the local `t`).
//!
//! The kinds, each named once here ([`EdgeKind`]):
//!
//! 1. a CALL (`Call`/`TailCall`) whose callee does not resolve to a body this rule
//!    holds;
//! 2. an INDIRECT call: the callee operand is not a constant `FnDef` (a function
//!    pointer, from a local, a field, a `static` or a `const`);
//! 3. a READ of a FOREIGN `static` (any use of its address, `safe static`
//!    included: it has no initializer the compiler validated) or of a foreign
//!    thread-local. A Rust `static`'s value was produced and validated by const
//!    evaluation, so reading it runs no code; a function pointer or trait object
//!    read OUT of one is charged where it is called (kinds 2 and 1);
//! 4. the CREATION of a function pointer (`ReifyFnPointer`, `ClosureFnPointer`) to a
//!    target this rule does not hold: the pointer can leave the body and be called
//!    by a caller that cannot resolve it;
//! 5. the CREATION of a vtable (an `Unsize` coercion to a trait object) whose
//!    concrete type reaches foreign user code, or whose principal trait lives in a
//!    crate this compilation neither verifies nor trusts;
//!
//!    Kinds 4 and 5 also cover a pointer CONST EVALUATION minted: the value of every
//!    constant the body uses (a promoted, a `const` item, a Rust `static`'s
//!    initializer, local or a dependency's) is walked allocation by allocation and
//!    each function pointer and vtable in it is judged as the cast would be
//!    (`judge_const_value`; r20, 2026-10-07);
//! 6. DROP glue that is not closed (`memory_safe_drop_glue_open_reason`);
//! 7. INLINE ASSEMBLY (`InlineAsm`): machine code no rule here models. Under
//!    `AssumedTotal` an `asm!` the sysroot's own inlined code owns is the
//!    sysroot's, as for its foreign items; memory-safe holds none;
//! 8. (memory-safe only) a masked fail-closed source of the print-grace scan
//!    (`function_has_masked_fail_closed_dispatch`).
//!
//! The two RULES ([`EdgeRule`]) differ only in which callees they hold:
//!
//! * [`EdgeRule::MemorySafeAssumption`] holds a LOCAL, non-foreign,
//!   non-`#[trust::skip]` item with MIR and nothing else: memory-safe refuses the
//!   absent-callee charge for a sysroot callee too;
//! * [`EdgeRule::AssumedTotal`] also holds an authentic foundational (core / alloc /
//!   std) callee whose instantiation reaches no foreign user code: totality is
//!   the assumption, and the sysroot is the TCB every lane already trusts for
//!   validity. A foreign item or foreign static in a scope inlined from the
//!   sysroot is the sysroot's own, as before.
//!
//! FAIL-CLOSED BY CONSTRUCTION: every shape not positively classified as held is an
//! edge (an unresolvable or virtual callee, a shim this file does not list, a type
//! parameter's drop).
//!
//! A local GENERIC callee (and a local generic closure, fn item, destructor or
//! surface impl method) is held only at an instantiation whose MIR, substituted at
//! the concrete arguments, has no edge of its own: the INSTANCE walk at the end of
//! this file (INSTANCE-WALK-1, 2026-10-14). Its polymorphic body says nothing about
//! which impl a call at `T` lands in.
//!
//! A local `#[trust::assume_total]` callee needs no arm of its own: it is skipped
//! only when THIS enumeration, under `AssumedTotal`, found no edge in it; otherwise
//! it is verified in full like any other local body. So the induction holds.

use std::cell::RefCell;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::interpret::{AllocId, ConstAllocation, GlobalAlloc, Scalar};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    Body, CastKind, ConstOperand, ConstValue, Location, Operand, Rvalue, SourceScope,
    TerminatorKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LOCAL_CRATE};

use super::validity_transmute::scope_is_inlined_from_sysroot;
use super::{
    callee_instantiation_reaches_foreign_user_code, callee_is_sysroot_fmt_machinery,
    crate_is_authentic_foundational, function_has_masked_fail_closed_dispatch,
    local_item_is_held_to_this_rule, memory_safe_drop_glue_open_reason,
    ty_reaches_foreign_user_code,
};

/// The kinds of edge into unverified code. See the module doc.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EdgeKind {
    Call,
    IndirectCall,
    ForeignStaticRead,
    FnPointerCreation,
    VtableCreation,
    DropGlue,
    InlineAsm,
    MaskedSource,
}

/// One edge: its kind and a human description (it names a callee or a type, so
/// it is rendered with no trimmed paths).
#[derive(Clone, Debug)]
pub(super) struct UnverifiedEdge {
    pub(super) kind: EdgeKind,
    pub(super) what: String,
}

/// Which callees a rule holds. See the module doc.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EdgeRule {
    MemorySafeAssumption,
    AssumedTotal,
}

/// Every edge of `body` into code `rule` does not hold, in body order (terminator
/// edges and statement edges of a block together, then the masked source).
pub(super) fn unverified_edges<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rule: EdgeRule,
) -> Vec<UnverifiedEdge> {
    // The reasons print types: a trimmed path in a compile that emits no
    // diagnostic ICEs at teardown (see `probe_label`).
    let edges = with_no_trimmed_paths!(unverified_edges_untrimmed(tcx, body, rule));
    for edge in &edges {
        tracing::trace!(
            "Trust unverified edge ({rule:?}) of {:?}: {:?} — {}",
            body.source.def_id(),
            edge.kind,
            edge.what
        );
    }
    edges
}

fn unverified_edges_untrimmed<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rule: EdgeRule,
) -> Vec<UnverifiedEdge> {
    let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    let mut scan = EdgeScan { tcx, body, typing_env, rule, edges: Vec::new() };
    scan.visit_body(body);
    let mut edges = scan.edges;
    if rule == EdgeRule::MemorySafeAssumption && function_has_masked_fail_closed_dispatch(tcx, body)
    {
        edges.push(UnverifiedEdge {
            kind: EdgeKind::MaskedSource,
            what: "a masked fail-closed source (a dependency call or function value, or foreign \
                   drop glue)"
                .to_string(),
        });
    }
    edges
}

struct EdgeScan<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    rule: EdgeRule,
    edges: Vec<UnverifiedEdge>,
}

impl<'tcx> EdgeScan<'_, 'tcx> {
    fn push(&mut self, kind: EdgeKind, what: String) {
        self.edges.push(UnverifiedEdge { kind, what });
    }

    fn in_sysroot_scope(&self, scope: SourceScope) -> bool {
        scope_is_inlined_from_sysroot(self.tcx, self.body, scope)
    }

    /// Does `rule` hold the function `def_id` instantiated at `args`? See
    /// [`holds_target`], which this delegates to.
    fn holds_target(
        &self,
        def_id: DefId,
        args: ty::GenericArgs<'tcx>,
        in_sysroot_scope: bool,
    ) -> bool {
        holds_target(self.tcx, self.typing_env, self.rule, def_id, args, in_sysroot_scope)
    }

    fn judge_call(&mut self, func: &Operand<'tcx>, location: Location) {
        let bb = location.block;
        let Some((def_id, args)) = func.const_fn_def() else {
            self.push(
                EdgeKind::IndirectCall,
                format!("a call through a function pointer in {bb:?}"),
            );
            return;
        };
        let in_sysroot = self.in_sysroot_scope(self.body.source_info(location).scope);
        if !self.holds_target(def_id, args, in_sysroot) {
            let callee = self.tcx.def_path_str(def_id);
            // The instance walk's reason, when that is why a local generic callee
            // is not held (its answer is cached, so this asks nothing new).
            let detail = match ty::Instance::try_resolve(self.tcx, self.typing_env, def_id, args) {
                Ok(Some(instance)) => match instance.def {
                    ty::InstanceKind::Item(did) if did.is_local() => {
                        local_instance_unverified_reason(self.tcx, did, instance.args)
                    }
                    _ => None,
                },
                _ => None,
            };
            match detail {
                Some(detail) => {
                    self.push(EdgeKind::Call, format!("`{callee}` in {bb:?} ({detail})"))
                }
                None => self.push(EdgeKind::Call, format!("`{callee}` in {bb:?}")),
            }
        }
    }

    fn judge_static(&mut self, did: DefId, location: Location) {
        if !self.tcx.is_foreign_item(did) {
            return;
        }
        if self.rule == EdgeRule::AssumedTotal
            && self.in_sysroot_scope(self.body.source_info(location).scope)
        {
            return;
        }
        let name = self.tcx.def_path_str(did);
        self.push(
            EdgeKind::ForeignStaticRead,
            format!(
                "a read of the foreign static `{name}` in {:?} (no initializer this compilation \
                 validated)",
                location.block
            ),
        );
    }
}

/// Does `rule` hold the function `def_id` instantiated at `args` — a body this
/// crate holds by induction, or (AssumedTotal) the trusted sysroot at an
/// instantiation that reaches no foreign user code? `typing_env` is the calling
/// body's.
///
/// Trust (2026-10-10, CALL-REACH-1 phase 1): factored out of
/// `EdgeScan::holds_target` (which now only delegates here, unchanged) so the
/// call-reach producer (`sysroot_drop_reach::call_site_reach`) can ask the SAME
/// ruled type rule as its pre-filter without an `EdgeScan` or a body.
pub(super) fn holds_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    rule: EdgeRule,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
    in_sysroot_scope: bool,
) -> bool {
    let resolved = match ty::Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(instance)) => instance,
        // Unresolvable here (a trait method at a type parameter of a GENERIC
        // body) or an error: the code it runs is chosen by an instantiation this
        // body cannot see, so it is not held. Holding it "because the caller's
        // call names the type" is NOT sound today: a VERIFIED caller's call to a
        // local `assume_total` generic is not charged at its type arguments.
        // MEASURED on stage 1 of this change with such an arm: `#[trust::
        // assume_total] fn run<I: Iterator<Item = u32>>(it: I) -> Option<u32> {
        // it.last() }` called as `run(dep::It(1))` (a verify-off iterator whose
        // `next` writes through null) from a verified `f` built rc=0 in default,
        // strict and memory-safe and the binary died with SIGSEGV (139), as on
        // `ae0494648a`.
        Ok(None) | Err(_) => return false,
    };
    match rule {
        // Trust (2026-10-14, INSTANCE-WALK-1): a local GENERIC body is held only at
        // an instantiation whose substituted MIR has no edge of its own (see
        // [`local_instance_unverified_reason`]).
        EdgeRule::MemorySafeAssumption => matches!(
            resolved.def,
            ty::InstanceKind::Item(did) if local_item_is_held_to_this_rule(tcx, did)
                && local_instance_unverified_reason(tcx, did, resolved.args).is_none()
        ),
        EdgeRule::AssumedTotal => {
            let did = match resolved.def {
                // A dispatch the compiler resolves only at run time.
                ty::InstanceKind::Virtual(..) | ty::InstanceKind::Shim(ty::ShimKind::FnPtr(..)) => {
                    return false;
                }
                ty::InstanceKind::Item(did) if did.is_local() => {
                    // A local foreign item called from a scope the sysroot's
                    // own inlined code owns is the sysroot's declaration. A local
                    // body is held only at type arguments that reach no foreign
                    // user code: a local `assume_total` GENERIC is skipped as a
                    // whole, so its instance at a dependency's type runs that
                    // type's code unverified.
                    //
                    // Trust (2026-10-14, INSTANCE-WALK-1): and type arguments that
                    // reach no foreign code are not enough either: what the instance
                    // CALLS at them is decided by which impl each call resolves to,
                    // and `g::<u32>` dispatching `<u32 as dep::Act2>::a2` runs a
                    // verify-off dependency body although `u32` is foundational. So
                    // the instance's own MIR at those arguments is walked as well.
                    return (local_item_is_held_to_this_rule(tcx, did)
                        && !local_instance_args_reach_foreign(tcx, did, resolved.args)
                        && local_instance_unverified_reason(tcx, did, resolved.args).is_none())
                        || (in_sysroot_scope && tcx.is_foreign_item(did));
                }
                other => other.def_id(),
            };
            // Anything else is the sysroot's (an item, an intrinsic, a shim
            // such as drop glue or a closure's `call_once`), at an
            // instantiation whose type arguments decide what user code it
            // runs: both the call as spelled and the resolved instance are
            // asked.
            if !crate_is_authentic_foundational(tcx, did.krate)
                && !trust_mir_extract::def_is_in_std_hash_table_crate(tcx, did)
            {
                return false;
            }
            !instantiation_reaches_foreign(tcx, def_id, args)
                && !args_reach_foreign(tcx, resolved.args)
        }
    }
}

/// The type arguments of a LOCAL instance, asked as `ty_reaches_foreign_user_code`
/// asks them. A closure-like body's arguments also carry its synthetic kind,
/// signature and witness types, which are no value it holds (a closure's
/// signature is spelled as a `fn` pointer type and would read as one): for it the
/// parent's type arguments and the captured upvars are asked instead. MEASURED on
/// stage 1 of this change before this split: `#[trust::assume_total] fn p(y: u32)
/// -> u32 { let c = |x: u32| x + 1; c(y) }` was revoked on "`std::ops::Fn::call` in
/// bb0".
fn local_instance_args_reach_foreign<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    let mut ask = |parent: &[ty::GenericArg<'tcx>], upvars: &[Ty<'tcx>]| {
        parent
            .iter()
            .filter_map(|arg| arg.as_type())
            .chain(upvars.iter().copied())
            .any(|t| value_ty_reaches_foreign(tcx, t, &mut memo))
    };
    if matches!(tcx.def_kind(did), DefKind::Closure | DefKind::SyntheticCoroutineBody) {
        match *tcx.type_of(did).instantiate_identity().skip_norm_wip().kind() {
            ty::Closure(..) => {
                let c = args.as_closure();
                return ask(c.parent_args(), c.upvar_tys());
            }
            ty::CoroutineClosure(..) => {
                let c = args.as_coroutine_closure();
                return ask(c.parent_args(), c.upvar_tys());
            }
            ty::Coroutine(..) => {
                let c = args.as_coroutine();
                return ask(c.parent_args(), c.upvar_tys());
            }
            // Not a shape this file can split: every argument is asked.
            _ => {}
        }
    }
    args_reach_foreign(tcx, args)
}

fn args_reach_foreign<'tcx>(tcx: TyCtxt<'tcx>, args: ty::GenericArgs<'tcx>) -> bool {
    let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    args.types().any(|t| value_ty_reaches_foreign(tcx, t, &mut memo))
}

/// The sysroot callee's instantiation reach. The formatting machinery takes
/// values that carry an `unsafe fn` formatter pointer by construction, so only
/// its type arguments (`Argument::new_display::<T>`) are asked for it.
fn instantiation_reaches_foreign<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if callee_is_sysroot_fmt_machinery(tcx, def_id) {
        return args_reach_foreign(tcx, args);
    }
    if def_id.is_local() {
        return args_reach_foreign(tcx, args);
    }
    if !callee_instantiation_reaches_foreign_user_code(tcx, def_id, args) {
        return false;
    }
    // The one value-borne reach this rule charges ELSEWHERE: a `fmt::Arguments`
    // handed to a sysroot sink (`std::io::_print`, `alloc::fmt::format`). Its
    // formatters are minted where it is packed — an `Argument::new_*::<T>` call
    // (a call edge above, asked at `T`) or, once that is inlined, a reified
    // `<T as Display>::fmt` (a function-pointer edge) — in this body, or by the
    // caller that packed a received one, which is judged on its own. Every other
    // input that reaches foreign user code (a `&dyn Trait`, a `Waker`, a function
    // pointer) stays an edge. MEASURED on stage 1 of this change before this arm:
    // `#[trust::assume_total] fn print_total(x: u32) { println!("{x}") }` was
    // revoked on "`std::io::_print` in bb2".
    if args_reach_foreign(tcx, args) {
        return true;
    }
    let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
    tcx.fn_sig(def_id).instantiate(tcx, args).skip_binder().inputs().iter().any(|&input| {
        !ty_is_fmt_arguments(tcx, input) && value_ty_reaches_foreign(tcx, input, &mut memo)
    })
}

impl<'tcx> Visitor<'tcx> for EdgeScan<'_, 'tcx> {
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                self.judge_call(func, location);
            }
            // A `Drop` runs code as surely as a `Call` does. See
            // `memory_safe_drop_glue_open_reason`.
            TerminatorKind::Drop { place, .. } => {
                let tcx = self.tcx;
                let drop_ty = place.ty(&self.body.local_decls, tcx).ty;
                let drop_ty = tcx
                    .normalize_erasing_regions(self.typing_env, ty::Unnormalized::new_wip(drop_ty));
                if let Some(open) = memory_safe_drop_glue_open_reason(tcx, self.typing_env, drop_ty)
                {
                    self.push(
                        EdgeKind::DropGlue,
                        format!("the drop glue of `{drop_ty}` in {:?} ({open})", location.block),
                    );
                }
            }
            TerminatorKind::InlineAsm { .. } => {
                let in_sysroot = self.in_sysroot_scope(self.body.source_info(location).scope);
                if !(self.rule == EdgeRule::AssumedTotal && in_sysroot) {
                    self.push(
                        EdgeKind::InlineAsm,
                        format!("inline assembly in {:?}", location.block),
                    );
                }
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        let tcx = self.tcx;
        match rvalue {
            Rvalue::ThreadLocalRef(did) => self.judge_static(*did, location),
            Rvalue::Cast(
                CastKind::PointerCoercion(
                    PointerCoercion::ReifyFnPointer(_) | PointerCoercion::ClosureFnPointer(_),
                    _,
                ),
                operand,
                _,
            ) => {
                let source = operand.ty(&self.body.local_decls, tcx);
                let held = match *source.kind() {
                    ty::FnDef(did, args) => {
                        let in_sysroot =
                            self.in_sysroot_scope(self.body.source_info(location).scope);
                        self.holds_target(did, args.skip_binder(), in_sysroot)
                    }
                    // The closure's own body, held by induction when it is local.
                    // Its upvars are asked as `ty_reaches_foreign_user_code` asks a
                    // closure (the signature in its args is not a value it holds).
                    ty::Closure(did, _) => {
                        let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
                        local_item_is_held_to_this_rule(tcx, did)
                            && !ty_reaches_foreign_user_code(tcx, source, &mut memo)
                    }
                    _ => false,
                };
                if !held {
                    self.push(
                        EdgeKind::FnPointerCreation,
                        format!(
                            "a function pointer to `{source}` created in {:?}, callable where \
                             its target cannot be resolved",
                            location.block
                        ),
                    );
                }
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                operand,
                target,
            ) => {
                let source = operand.ty(&self.body.local_decls, tcx);
                if let Some(reason) = self.vtable_creation_reason(source, *target) {
                    self.push(
                        EdgeKind::VtableCreation,
                        format!(
                            "a vtable for `{source}` as `{target}` in {:?} ({reason})",
                            location.block
                        ),
                    );
                }
            }
            _ => {}
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        if let Some(did) = constant.check_static_ptr(self.tcx) {
            self.judge_static(did, location);
        }
        self.judge_const_value(constant, location);
    }
}

/// The allocations one constant's walk may visit before it answers "an edge"
/// (fail-closed). A backstop: a constant's pointer graph is its own literal data.
const CONST_ALLOC_WALK_MAX: usize = 4096;

impl<'tcx> EdgeScan<'_, 'tcx> {
    /// Kinds 4 and 5 for a pointer CONST EVALUATION minted: a function pointer or a
    /// vtable inside the value of a constant this body uses — a promoted (`&(dep::f as
    /// fn())`), a `const` item, or a Rust `static`'s initializer, local or a
    /// dependency's. `visit_body` never enters a promoted's MIR and kind 3 exempts a
    /// Rust static's READ, so the casts that minted these pointers are in no body this
    /// scan sees; the evaluated value is what can leave the body, so the value's
    /// allocations are walked (as the mono collector walks them) and every function
    /// and vtable in them is judged as the cast would be.
    ///
    /// Trust (r20, 2026-10-07), MEASURED on stage 1 `a92f7478b6`, memory-safe, each
    /// body classifier-skipped through `let _q = &raw const s.a;`: returning `F` for
    /// `const F: fn() = dep::null_fn`, `dep::DEP_FP`, a local `static G: fn() =
    /// dep::null_fn`, `*&(dep::null_fn as fn())`, `dep::DEP_DYN`, a local `const C:
    /// &dyn dep::Act = &dep::W(3)`, or `*&(&dep::W(3) as &dyn dep::Act)` built rc=0
    /// with an `assumption:addr-of-field` row, and a verify-off `main` that called the
    /// returned pointer died with SIGSEGV (139), while the same pointers minted by a
    /// cast in the body were refused.
    fn judge_const_value(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        let tcx = self.tcx;
        let ty = constant.const_.ty();
        if !ty_may_carry_pointer(ty) {
            return;
        }
        let bb = location.block;
        let value = match constant.const_.eval(tcx, self.typing_env, constant.span) {
            Ok(value) => value,
            Err(_) => {
                self.push(
                    EdgeKind::FnPointerCreation,
                    format!(
                        "a constant of type `{ty}` in {bb:?} this scan cannot evaluate, which \
                         may carry a function pointer or vtable"
                    ),
                );
                return;
            }
        };
        let root = match value {
            ConstValue::Scalar(Scalar::Ptr(ptr, _)) => ptr.provenance.alloc_id(),
            ConstValue::Slice { alloc_id, .. } | ConstValue::Indirect { alloc_id, .. } => alloc_id,
            ConstValue::Scalar(Scalar::Int(_)) | ConstValue::ZeroSized => return,
        };
        let in_sysroot = self.in_sysroot_scope(self.body.source_info(location).scope);
        let mut seen: FxHashSet<AllocId> = FxHashSet::default();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            if seen.len() > CONST_ALLOC_WALK_MAX {
                self.push(
                    EdgeKind::FnPointerCreation,
                    format!("a constant in {bb:?} whose pointer graph is too large to scan"),
                );
                return;
            }
            let push_ptrs = |alloc: ConstAllocation<'tcx>, stack: &mut Vec<AllocId>| {
                stack.extend(alloc.inner().provenance().ptrs().values().map(|p| p.alloc_id()));
            };
            match tcx.try_get_global_alloc(id) {
                Some(GlobalAlloc::Memory(alloc)) => push_ptrs(alloc, &mut stack),
                Some(GlobalAlloc::Function { instance }) => {
                    if !self.holds_target(instance.def_id(), instance.args, in_sysroot) {
                        self.push(
                            EdgeKind::FnPointerCreation,
                            format!(
                                "a function pointer to `{instance}` in a constant used in \
                                 {bb:?}, callable where its target cannot be resolved"
                            ),
                        );
                    }
                }
                Some(GlobalAlloc::VTable(concrete, predicates)) => {
                    if let Some(reason) = self.vtable_reason(concrete, predicates) {
                        self.push(
                            EdgeKind::VtableCreation,
                            format!(
                                "a vtable for `{concrete}` in a constant used in {bb:?} \
                                 ({reason})"
                            ),
                        );
                    }
                }
                Some(GlobalAlloc::Static(did)) => {
                    if tcx.is_foreign_item(did) {
                        self.judge_static(did, location);
                    } else if crate_is_authentic_foundational(tcx, did.krate) {
                        // The sysroot's own static: its initializer is the TCB's.
                    } else if tcx.is_thread_local_static(did) {
                        self.push(
                            EdgeKind::FnPointerCreation,
                            format!("a thread-local static in a constant used in {bb:?}"),
                        );
                    } else {
                        match tcx.eval_static_initializer(did) {
                            Ok(alloc) => push_ptrs(alloc, &mut stack),
                            Err(_) => self.push(
                                EdgeKind::FnPointerCreation,
                                format!(
                                    "the static `{}` in a constant used in {bb:?}, whose \
                                     initializer this scan cannot evaluate",
                                    tcx.def_path_str(did)
                                ),
                            ),
                        }
                    }
                }
                Some(GlobalAlloc::TypeId { .. }) => {}
                None => self.push(
                    EdgeKind::FnPointerCreation,
                    format!("a constant in {bb:?} with a dangling allocation"),
                ),
            }
        }
    }
}

/// Could a value of `ty` hold a pointer (and so a function pointer or vtable)?
/// Only plain scalars, `str`, a `FnDef` and arrays, slices and tuples of them are
/// known not to; every other type is evaluated and walked.
fn ty_may_carry_pointer(ty: Ty<'_>) -> bool {
    match *ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Str
        | ty::Never
        | ty::FnDef(..) => false,
        ty::Array(inner, _) | ty::Slice(inner) | ty::Pat(inner, _) => ty_may_carry_pointer(inner),
        ty::Tuple(elems) => elems.iter().any(ty_may_carry_pointer),
        _ => true,
    }
}

impl<'tcx> EdgeScan<'_, 'tcx> {
    /// Why an `Unsize` coercion from `source` to `target` mints a vtable whose
    /// entries run code this rule does not hold, or `None` when it mints none (a
    /// slice coercion) or a held one.
    fn vtable_creation_reason(&self, source: Ty<'tcx>, target: Ty<'tcx>) -> Option<String> {
        let Some((source_pointee, target_pointee)) = unsize_tails(source, target) else {
            // Not a coercion this file can read: fail closed only when the target
            // names a trait object anywhere.
            return target
                .walk()
                .filter_map(|a| a.as_type())
                .any(|t| matches!(t.kind(), ty::Dynamic(..)))
                .then(|| "a coercion to a trait object this scan cannot read".to_string());
        };
        let ty::Dynamic(predicates, ..) = *target_pointee.kind() else { return None };
        // An upcast from one trait object to another reuses the vtable the first
        // one carries: that vtable was charged where it was minted.
        if matches!(source_pointee.kind(), ty::Dynamic(..)) {
            return None;
        }
        self.vtable_reason(source_pointee, predicates)
    }

    /// Why a vtable of `concrete` for the trait object `predicates` runs code this
    /// rule does not hold, or `None`.
    fn vtable_reason(
        &self,
        source_pointee: Ty<'tcx>,
        predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    ) -> Option<String> {
        let tcx = self.tcx;
        if let Some(principal) = predicates.principal_def_id()
            && !principal.is_local()
            && !crate_is_authentic_foundational(tcx, principal.krate)
        {
            return Some(format!(
                "its trait `{}` is in a crate this compilation does not verify",
                tcx.def_path_str(principal)
            ));
        }
        let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
        ty_reaches_foreign_user_code(tcx, source_pointee, &mut memo)
            .then(|| format!("`{source_pointee}` reaches code this compilation does not verify"))
    }
}

/// `ty_reaches_foreign_user_code`, except that a `PhantomData<T>` (core's
/// `phantom_data` lang item) reaches nothing: it holds no value, and every impl a
/// sysroot callee can use on it is core's own and never runs `T`'s code (a
/// dependency's trait cannot bound a sysroot fn). MEASURED on stage 1 of this change
/// before this arm: `#[trust::assume_total]` over
/// `core::hint::black_box(PhantomData::<fn() -> u32>)` was revoked on
/// "`std::hint::black_box` in bb0" (`assume_total_does_not_cover_callee_requires.rs`,
/// `phantom_certify`). Only a TOP-LEVEL argument is unwrapped; a `PhantomData` nested
/// in another type is asked as that type is.
fn value_ty_reaches_foreign<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    memo: &mut FxHashMap<Ty<'tcx>, bool>,
) -> bool {
    if let ty::Adt(adt, _) = *ty.kind()
        && adt.is_phantom_data()
    {
        return false;
    }
    ty_reaches_foreign_user_code(tcx, ty, memo)
}

/// Is `ty` core's `fmt::Arguments` (the `format_arguments` lang item), possibly
/// behind references?
fn ty_is_fmt_arguments<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let mut ty = ty;
    while let ty::Ref(_, inner, _) = *ty.kind() {
        ty = inner;
    }
    matches!(*ty.kind(), ty::Adt(adt, _)
        if tcx.is_lang_item(adt.did(), rustc_attr_ir::lang_items::LangItem::FormatArguments))
}

/// The pair of types an `Unsize` coercion actually unsizes: the pointees of two
/// references or raw pointers, or the first differing type arguments of two
/// instances of one smart pointer (`Box`, `Rc`, `Arc`, `Pin<Box<_>>`, ...),
/// followed down while both sides keep the same pointer shape.
fn unsize_tails<'tcx>(source: Ty<'tcx>, target: Ty<'tcx>) -> Option<(Ty<'tcx>, Ty<'tcx>)> {
    let mut pair = (source, target);
    for _ in 0..16 {
        let next = match (*pair.0.kind(), *pair.1.kind()) {
            (ty::Ref(_, a, _) | ty::RawPtr(a, _), ty::Ref(_, b, _) | ty::RawPtr(b, _)) => (a, b),
            (ty::Adt(da, aa), ty::Adt(db, ab)) if da == db => {
                aa.types().zip(ab.types()).find(|(x, y)| x != y)?
            }
            _ => return None,
        };
        let same_shape = match (*next.0.kind(), *next.1.kind()) {
            (ty::Ref(..) | ty::RawPtr(..), ty::Ref(..) | ty::RawPtr(..)) => true,
            (ty::Adt(da, _), ty::Adt(db, _)) => da == db,
            _ => false,
        };
        if !same_shape {
            return Some(next);
        }
        pair = next;
    }
    None
}

// ---- The INSTANCE walk (Trust 2026-10-14, INSTANCE-WALK-1) ------------------------
//
// A local generic body is "held by induction" only for what its POLYMORPHIC body
// does: it is verified, refused, or admitted on a row of its own. Which impl each of
// its calls lands in, which destructor each of its drops runs and which function a
// pointer it mints names are decided by its type arguments, and none of that is in
// the polymorphic body. MEASURED on stage 1 `d28d17dc2` with a verify-off dependency
// whose `null_fn` writes through null (`unverified_edge_instance_dep.rs`): an
// `#[trust::assume_total] fn t() -> u32 { g(&5u32) }` with a local `g<T: dep::Act2>(x:
// &T) -> u32 { x.a2() }` and the dependency's `impl Act2 for u32` built rc=0 in the
// default and strict lanes and the binary died with SIGSEGV (139); so did a dependency
// blanket impl, an impl for `()`, a `&str` instance, a fn pointer to `T::a2` minted
// in the generic, a local blanket impl over a dependency trait, a transitive generic,
// an inherent method of a local generic ADT, a local generic ADT's trait impl handed
// to `Iterator::count`, and a local generic ADT's `Drop` (bare, in an `Option`, a
// `Box`, a tuple, an array, a `Vec`). `u32`, `()` and `&str` reach no foreign code,
// so the type-argument check (`local_instance_args_reach_foreign`) held every one.
//
// THE WALK. For a local generic body at CONCRETE arguments, its MIR (fetched as
// `sysroot_drop_reach` fetches a local body: the elaborated snapshot when
// `optimized_mir` would cycle, `optimized_mir` otherwise, fail-closed when neither is
// readable) is instantiated at those arguments under `TypingEnv::fully_monomorphized`
// and scanned by THIS file's `EdgeScan` under `EdgeRule::AssumedTotal`: every call is
// resolved at the arguments, every `Drop` type, cast and constant is the substituted
// one, and a local generic callee it reaches is walked in turn. Any edge is an edge of
// the caller. The walk asks `AssumedTotal` under both rules: the instance's own
// sysroot calls are charged by the polymorphic body's verification, and what the
// instantiation adds is code nothing verifies, which is what that rule names.
//
// Recursion: an instance already being walked (same `DefId`, same interned
// arguments) answers "no edge" coinductively (the outer frame is scanning that very
// body); the same `DefId` at OTHER arguments (polymorphic recursion) and a chain
// deeper than [`INSTANCE_WALK_MAX_DEPTH`] answer "an edge" (fail-closed). An answer
// of "an edge" is always cached; "no edge" only for an outermost walk, whose every
// coinductive assumption was discharged inside it.
//
// An instance whose arguments still name a type or const PARAMETER is not walked: it
// is asked in a generic body, where the existing rules answer (a type parameter
// reaches foreign code; a call at it is unresolvable), and the instance is walked
// again where its arguments become concrete, by the walk of the instance enclosing it.

/// How many nested local generic instances one walk follows before it answers "an
/// edge" (fail-closed).
const INSTANCE_WALK_MAX_DEPTH: usize = 32;

/// (`DefId`, address of the interned argument list).
type InstanceKey = (DefId, usize);

// Trust: GenericArgs is a Copy wrapper, so its stack address is not an instance
// identity. Both settlement and the walk must key the same interned allocation;
// InstanceWalkState confines that address to its originating compilation session.
#[expect(deprecated, reason = "session-scoped memo identity for the current interned GenericArgs")]
fn instance_key(did: DefId, args: ty::GenericArgs<'_>) -> InstanceKey {
    (did, args.as_ptr() as usize)
}

#[derive(Default)]
struct InstanceWalkState {
    /// The compilation the entries belong to: the local crate's `StableCrateId` and
    /// the session's address. Interned argument addresses are meaningful only
    /// within one.
    session: (u64, usize),
    in_progress: Vec<InstanceKey>,
    done: FxHashMap<InstanceKey, Option<String>>,
}

// Trust: only a completed no-edge walk may leave this module as an independent
// call-walk leaf. A recursive `None` inside the walk is only provisional.
impl InstanceWalkState {
    fn has_settled_no_edge(&self, session: (u64, usize), key: InstanceKey) -> bool {
        self.session == session && matches!(self.done.get(&key), Some(None))
    }
}

thread_local! {
    static INSTANCE_WALK: RefCell<InstanceWalkState> =
        RefCell::new(InstanceWalkState::default());
}

/// Pops the walk's frame on every exit, unwinding included.
struct InstanceWalkFrame;

impl Drop for InstanceWalkFrame {
    fn drop(&mut self) {
        INSTANCE_WALK.with(|cell| {
            cell.borrow_mut().in_progress.pop();
        });
    }
}

/// Is the local body `did` generic, so that its instances can differ? A closure-like
/// body's own generics always carry its synthetic kind/signature/upvar parameters,
/// so for it the item it is type-checked with is asked.
pub(super) fn local_instance_is_generic(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let root = if tcx.is_typeck_child(did) { tcx.typeck_root_def_id(did) } else { did };
    tcx.generics_of(root).requires_monomorphization(tcx)
}

/// Trust: may an independent call walk stop at this LOCAL instance? The caller
/// must first check that the body is held and its instantiation reaches no foreign
/// code. A non-generic body retains that induction premise. A generic body also
/// needs a SETTLED no-edge walk: the internal same-instance coinductive `None`
/// must not become a persistent closed answer in `CALL_REACH_MEMO` before the
/// outer walk discovers a later edge. Nested no-edge answers are deliberately not
/// cached by the instance walk, so only its matching-session `done` entry closes.
pub(super) fn local_instance_has_settled_no_edge<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if !did.is_local() {
        return false;
    }
    if !local_instance_is_generic(tcx, did) {
        return true;
    }
    // The internal walk leaves parameter-containing arguments to its generic
    // caller's rules. That `None` is not a concrete no-edge result either.
    if args.has_non_region_param()
        || args.has_non_region_infer()
        || args.has_non_region_placeholders()
        || args.references_error()
        || args.has_escaping_bound_vars()
    {
        return false;
    }
    let args = tcx.erase_and_anonymize_regions(args);
    if local_instance_unverified_reason(tcx, did, args).is_some() {
        return false;
    }
    let key = instance_key(did, args);
    let session = (
        tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        std::ptr::from_ref(tcx.sess).cast::<()>() as usize,
    );
    INSTANCE_WALK.with(|cell| cell.borrow().has_settled_no_edge(session, key))
}

/// Why the LOCAL body `did`, instantiated at `args`, reaches code this compilation
/// does not verify through what its instantiation adds (see the section doc), or
/// `None` when it reaches none, is not generic, or is asked at arguments that still
/// name a parameter. Its reason prints paths: it renders them untrimmed itself.
pub(super) fn local_instance_unverified_reason<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<String> {
    if !did.is_local() || !local_instance_is_generic(tcx, did) {
        return None;
    }
    if args.has_non_region_param() {
        return None;
    }
    if args.has_non_region_infer()
        || args.has_non_region_placeholders()
        || args.references_error()
        || args.has_escaping_bound_vars()
    {
        return Some(format!(
            "`{}` is instantiated at arguments this scan cannot read",
            with_no_trimmed_paths!(tcx.def_path_str(did))
        ));
    }
    let args = tcx.erase_and_anonymize_regions(args);
    let key = instance_key(did, args);
    let session = (
        tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        std::ptr::from_ref(tcx.sess).cast::<()>() as usize,
    );
    enum Pre {
        Answer(Option<String>),
        Walk { outermost: bool },
    }
    let pre = INSTANCE_WALK.with(|cell| {
        let mut state = cell.borrow_mut();
        if state.session != session && state.in_progress.is_empty() {
            *state = InstanceWalkState { session, ..InstanceWalkState::default() };
        }
        if let Some(done) = state.done.get(&key) {
            return Pre::Answer(done.clone());
        }
        if state.in_progress.contains(&key) {
            return Pre::Answer(None);
        }
        let path = || with_no_trimmed_paths!(tcx.def_path_str(did));
        if state.in_progress.iter().any(|(outer, _)| *outer == did) {
            return Pre::Answer(Some(format!(
                "`{}` is reached again at other type arguments (polymorphic recursion)",
                path()
            )));
        }
        if state.in_progress.len() >= INSTANCE_WALK_MAX_DEPTH {
            return Pre::Answer(Some(format!(
                "`{}` is nested too deep in generic instances to walk",
                path()
            )));
        }
        let outermost = state.in_progress.is_empty();
        state.in_progress.push(key);
        Pre::Walk { outermost }
    });
    let outermost = match pre {
        Pre::Answer(answer) => return answer,
        Pre::Walk { outermost } => outermost,
    };
    let answer = {
        let _frame = InstanceWalkFrame;
        with_no_trimmed_paths!(walk_local_instance(tcx, did, args))
    };
    if answer.is_some() || outermost {
        INSTANCE_WALK.with(|cell| {
            let mut state = cell.borrow_mut();
            if state.session == session {
                state.done.insert(key, answer.clone());
            }
        });
    }
    answer
}

/// The walk itself: the first edge of `did`'s MIR instantiated at `args` (concrete,
/// regions erased), rendered for a note.
fn walk_local_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<String> {
    let path = || tcx.def_path_str_with_args(did, args);
    let Some(local) = did.as_local() else {
        return Some(format!("`{}` is not a body of this crate", path()));
    };
    if matches!(tcx.def_kind(did), DefKind::Ctor(..)) {
        return None;
    }
    let body = if super::optimized_mir_query_would_cycle(tcx, did) {
        match tcx.mir_for_trust_verification(local) {
            Some(body) => body,
            None => return Some(format!("the MIR of `{}` is not readable here", path())),
        }
    } else if tcx.is_mir_available(did) {
        tcx.optimized_mir(did)
    } else {
        return Some(format!("`{}` has no MIR here", path()));
    };
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let instance = ty::Instance::new_raw(did, args);
    let Ok(mono) = instance.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        ty::EarlyBinder::bind(tcx, body.clone()),
    ) else {
        return Some(format!("the MIR of `{}` does not normalize at these arguments", path()));
    };
    let mut scan =
        EdgeScan { tcx, body: &mono, typing_env, rule: EdgeRule::AssumedTotal, edges: Vec::new() };
    scan.visit_body(&mono);
    scan.edges.first().map(|edge| format!("`{}` reaches {}", path(), edge.what))
}

/// Does the LOCAL fn item `did` at `args` — a value a sysroot callee can call —
/// reach code this compilation does not verify through its instantiation? A trait
/// method is resolved first; one that does not resolve to a local body at concrete
/// arguments answers `true` (fail-closed). For `ty_reaches_foreign_user_code`.
pub(super) fn local_fn_item_instance_reaches_unverified<'tcx>(
    tcx: TyCtxt<'tcx>,
    did: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if !local_instance_is_generic(tcx, did) || args.has_non_region_param() {
        return false;
    }
    if !matches!(
        tcx.def_kind(did),
        DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..) | DefKind::Closure
    ) {
        return true;
    }
    let args = tcx.erase_and_anonymize_regions(args);
    match ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), did, args) {
        Ok(Some(instance)) => match instance.def {
            ty::InstanceKind::Item(resolved) if resolved.is_local() => {
                local_instance_unverified_reason(tcx, resolved, instance.args).is_some()
            }
            _ => true,
        },
        Ok(None) | Err(_) => true,
    }
}

// Trust: exercise the settlement guard consumed by the real call-walk leaf.
#[cfg(test)]
mod tests;
