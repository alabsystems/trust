//! Trust (2026-10-05, DYN-ARG-PROVENANCE-1; docs/DECISION_QUEUE.md "OD-1" item 14
//! amendment): which trait objects a body's ARGUMENT can carry when no crate this
//! compilation does not see can call the body.
//!
//! OD-1 item 14 (`04c39335f3`) refutes a virtual call as class (c) of "L0 refutation
//! rows" when the trait object is one an adversary can construct
//! (`virtual_dispatch_is_adversarial`) AND the receiver is one of the body's own
//! arguments (`argument_root`): "the caller chooses the value". For a
//! body a downstream crate can call that is exactly right. For a PRIVATE function
//! it over-reaches: its only callers are this crate's own code, so the set of values
//! the argument can carry is the set this crate's call sites hand it, all of which
//! are visible here.
//!
//! The shape that raised it (preview2, stage 1 `c797f90c1`, clean-ck0
//! `nested_replace.rs:318`):
//!
//! ```text
//! fn map_children_depth(expr: &Term, depth: u32, f: &dyn Fn(&Term, u32) -> Term) -> Term
//! ```
//!
//! is private and both call sites pass `&|child, depth| …`, a closure they write.
//! That row nevertheless STAYS `failed` under this rule, correctly: one of the two
//! closures captures `env: &dyn Env`, which a public caller received, so calling `f`
//! can run a downstream `Env` impl. With closures that capture nothing adversarial
//! (`tests/ui/trust/instance_hypothesis/dyn_private_fn_local_values_stays_runtime_checked.rs`)
//! the refutation's reason — "a downstream impl may panic" — is false: no downstream
//! code can reach the call.
//!
//! The rule: a virtual call on argument `i` of a LOCAL function is NOT adversarial
//! when ([`dyn_argument_is_built_locally_at_every_call`]):
//!
//! * the function is a free fn or an INHERENT associated fn (never a trait method,
//!   never a closure or coroutine: those are called through dispatch this crate does
//!   not enumerate);
//! * it is public at NO effective-visibility level (not exported, not reachable,
//!   not reachable through `impl Trait`), carries no extern indicator (`no_mangle`,
//!   `export_name`, EII, …), and the crate defines no def-site-hygienic macro
//!   (`crate_defines_def_site_macro`: such a macro lets a downstream crate call a
//!   private function with ITS OWN arguments); a whole-program crate needs none of
//!   this — every trait there is sealed already;
//! * EVERY mention of the function in this crate's HIR bodies is the callee of a
//!   direct call (`h(..)`, `Self::h(..)`, `x.h(..)`) — a mention as a value (a fn
//!   pointer, `sym`, an argument to another function) can be called with anything;
//! * at every such call, argument `i`'s UNADJUSTED type is a pointer (`&`, `&mut`,
//!   `Box`) to a concrete value the call site builds whose dispatch target has a
//!   body in THIS crate — a local closure, a local free or inherent fn item with a
//!   body, or a local ADT (2026-10-06 review: a body-less fn item such as
//!   `<dyn Tr as Tr>::o`, an upstream fn, or a non-local pointee forwards the body's
//!   other arguments into code with no row here; [`pointer_to_locally_chosen`]) —
//!   no part of which (fields of every variant, generic
//!   arguments, closure upvars, pointees, transitively) has a trait-object,
//!   fn-pointer, type-parameter, alias, foreign, coroutine or error/inference type
//!   ([`pointer_to_locally_chosen`], [`value_type_is_closed`]). A forwarded `&dyn
//!   Tr` (the caller's own argument), a `&T`, an `impl Tr`, a `fn()` pointer, and a
//!   local wrapper or closure that CARRIES a forwarded trait object all keep the
//!   refutation.
//!
//! Errs toward "adversarial" (the refutation stands) on every uncertainty: a body
//! owner with no walkable HIR (a Clean-origin synthetic owner), no call site at all,
//! an argument index past the call's arguments.
//!
//! What it does NOT reopen: the soundness hole item 14 closed is that an open
//! dispatch a downstream crate can drive published `runtime_checked`, so
//! `--allow-l0-gaps` conditional-passed it. A forwarding chain `pub fn g(f: &dyn
//! Tr) { h(f) }` keeps `h`'s row `failed` (the call site's argument is a trait
//! object), and the row this rule relabels was never a found violation: it goes
//! back to the disclosed `runtime_checked` label the `local_dyn` control already
//! carries (a trait object the body builds itself), which strict and certify refuse.
//! The panic an impl's own body can raise is that body's row, not this one — which
//! is why the pointee's impl must be LOCAL: a body this crate does not have has no
//! row to carry it.

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::DefId;

use super::{crate_defines_def_site_macro, crate_types_are_whole_program};

/// Is every value the `param`-th argument (0-based, MIR argument `param + 1`) of
/// local function `fn_def` can carry a pointer to a concrete type one of this
/// crate's own call sites builds? `false` on any uncertainty. See the module doc.
pub(super) fn dyn_argument_is_built_locally_at_every_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_def: DefId,
    param: usize,
) -> bool {
    let Some(local) = fn_def.as_local() else { return false };
    if crate_types_are_whole_program(tcx) {
        // Not this rule's business: every trait is sealed there and the virtual arm
        // never fires. Answer the fail-closed default rather than walk the crate.
        return false;
    }
    let free_or_inherent = match tcx.def_kind(fn_def) {
        DefKind::Fn => true,
        DefKind::AssocFn => tcx.inherent_impl_of_assoc(fn_def).is_some(),
        _ => false,
    };
    if !free_or_inherent
        || tcx.effective_visibilities(()).public_at_level(local).is_some()
        || tcx.codegen_fn_attrs(fn_def).contains_extern_indicator()
        || crate_defines_def_site_macro(tcx)
    {
        return false;
    }
    let mut finder =
        CallSiteFinder { tcx, target: fn_def, param, typeck: None, calls: 0, escaped: false };
    for owner in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(owner), DefKind::SyntheticCoroutineBody) {
            // A by-move copy of its parent coroutine's body; the parent is walked.
            continue;
        }
        if crate::clean_origin_mir::is_clean_origin(tcx, owner) {
            // No HIR body to read: cannot rule a mention out.
            return false;
        }
        let Some(body) = tcx.hir_maybe_body_owned_by(owner) else { return false };
        finder.typeck = Some(tcx.typeck(owner));
        finder.visit_body(body);
        if finder.escaped {
            return false;
        }
    }
    finder.calls > 0
}

struct CallSiteFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    target: DefId,
    param: usize,
    typeck: Option<&'tcx ty::TypeckResults<'tcx>>,
    calls: usize,
    escaped: bool,
}

impl<'tcx> CallSiteFinder<'tcx> {
    fn typeck(&self) -> &'tcx ty::TypeckResults<'tcx> {
        self.typeck.expect("set before every body walk")
    }

    fn names_target(&self, expr: &hir::Expr<'_>) -> bool {
        match &expr.kind {
            hir::ExprKind::Path(qpath) => {
                self.typeck().qpath_res(qpath, expr.hir_id).opt_def_id() == Some(self.target)
            }
            _ => false,
        }
    }

    fn charge_call_argument(&mut self, argument: Option<&hir::Expr<'_>>) {
        self.calls += 1;
        let local = argument.is_some_and(|argument| {
            pointer_to_locally_chosen(self.tcx, self.typeck().expr_ty(argument))
        });
        if !local {
            self.escaped = true;
        }
    }
}

impl<'tcx> Visitor<'tcx> for CallSiteFinder<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if self.escaped {
            return;
        }
        match &expr.kind {
            hir::ExprKind::Call(callee, args) if self.names_target(callee) => {
                self.charge_call_argument(args.get(self.param));
                for arg in *args {
                    self.visit_expr(arg);
                }
                return;
            }
            hir::ExprKind::MethodCall(_, receiver, args, _)
                if self.typeck().type_dependent_def_id(expr.hir_id) == Some(self.target) =>
            {
                let argument =
                    if self.param == 0 { Some(*receiver) } else { args.get(self.param - 1) };
                self.charge_call_argument(argument);
                self.visit_expr(receiver);
                for arg in *args {
                    self.visit_expr(arg);
                }
                return;
            }
            // A mention that is not the callee of a direct call: the function escapes
            // as a value and can be called with anything.
            hir::ExprKind::Path(_) if self.names_target(expr) => {
                self.escaped = true;
                return;
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

/// Is `ty` (a call site's unadjusted argument type) a `&`, `&mut` or `Box` pointer
/// to a value whose whole type tree is closed ([`value_type_is_closed`]), and whose
/// own type is one whose dispatch target has a BODY IN THIS CRATE: a local closure,
/// a local free or inherent fn item with a body ([`fn_item_has_local_body`]), or a
/// local ADT?
///
/// Trust (2026-10-06, DYN-ARG-PROVENANCE-1 review): the exemption's premise is that
/// whatever the virtual call reaches is code with its OWN row here, so a panic it
/// can raise is that row's to report. That holds only when the pointee's impl of
/// the parameter's trait is local:
/// * a fn item with no body here (`<dyn Open as Open>::o`, an upstream or std fn)
///   is called through a builtin `Fn` shim that forwards the private body's OTHER,
///   adversarial argument into dispatch no row of this crate covers — measured:
///   `fn apply(f: &dyn Fn(&dyn Open) -> u32, t: &dyn Open) -> u32 { f(t) }` called
///   as `apply(&<dyn Open as Open>::o, t)` from a `pub fn` read `runtime_checked`
///   with no `failed` row in the crate, and a downstream `impl Open` panicked
///   through it (`dyn_private_fn_bodyless_or_upstream_callee_is_failed.rs` (1));
/// * a NON-local pointee (an upstream ADT, a scalar, `str`, a tuple, array or
///   slice, a `&X`) can carry an upstream impl of an upstream trait with no blanket
///   impl — `impl<T: ?Sized + Up> Visitor<T> for UpV`, `impl<V: ?Sized> Tr for &V`
///   — whose body, not in this crate, dispatches on the forwarded argument
///   (`dyn_private_fn_bodyless_or_upstream_callee_is_failed.rs` (2), through an
///   auxiliary crate).
/// A LOCAL closure, fn item or ADT cannot: orphan rules let another crate name it
/// only through a blanket impl (`Self` a type parameter), and a trait with one is
/// not adversarial (`virtual_dispatch_is_adversarial`) — except the `Fn` family,
/// whose impls for a closure or fn item are the builtin ones that call its local
/// body. Everything else keeps the refutation.
fn pointer_to_locally_chosen<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let pointee = match *ty.kind() {
        ty::Ref(_, pointee, _) => pointee,
        _ if ty.is_box() => ty.expect_boxed_ty(),
        _ => return false,
    };
    let local_dispatch_target = match *pointee.kind() {
        ty::Closure(def_id, _) => def_id.is_local(),
        ty::FnDef(def_id, _) => fn_item_has_local_body(tcx, def_id),
        ty::Adt(def, _) => def.did().is_local(),
        _ => false,
    };
    local_dispatch_target && value_type_is_closed(tcx, pointee, &mut FxHashSet::default(), 0)
}

/// Is `def_id` a LOCAL free fn or inherent associated fn with a body in this crate
/// (not a foreign-block declaration, a constructor, a trait method or a virtual
/// shim)? Only such a fn item's calls land in code with its own row here.
fn fn_item_has_local_body(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else { return false };
    let free_or_inherent = match tcx.def_kind(def_id) {
        DefKind::Fn => true,
        DefKind::AssocFn => tcx.inherent_impl_of_assoc(def_id).is_some(),
        _ => false,
    };
    free_or_inherent && !tcx.is_foreign_item(def_id) && tcx.hir_maybe_body_owned_by(local).is_some()
}

/// Can a value of type `ty` carry, anywhere inside it, a callable the call site did
/// not choose? `true` only when no part of the value — through references, raw
/// pointers, `Box`, tuple/array/slice elements, EVERY field of every variant of an
/// ADT and every generic type argument of it, and every captured upvar of a
/// closure — has a trait-object, fn-pointer,
/// type-parameter, alias, foreign, coroutine or error/inference type.
///
/// The fields and upvars matter: a local wrapper (`struct W<'a>(&'a dyn Tr)`, or a
/// closure capturing `t: &dyn Tr`) unsized at the call site hands the private body a
/// vtable whose impl is the wrapper's, but that impl calls the forwarded trait
/// object through a FIELD projection, which item 14's original walk declined; without
/// this walk `pub fn g(t: &dyn Tr) { h(&W(t)) }` would publish no `failed` row anywhere.
/// (2026-10-06, merge with OD-1-RG-CONCRETE: `dyn_receiver_root::argument_root` now
/// follows a field of a fn or method argument, so a wrapper's `impl Tr` row refutes on
/// its own — but it still declines a field of a CLOSURE's environment, which is how a
/// capturing closure reads the forwarded object, so this walk stays load-bearing.
/// 2026-10-11, CLOSURE-CAPTURE-ROOT: a capture of the closure's PARENT's immutable
/// parameter is now followed, so `pub fn g(t: &dyn Tr) { h(&|| t.m()) }`'s closure
/// row refutes on its own; a capture of a `let` local still declines, so this walk
/// still decides that shape.)
/// Measured instance of the shape: ty `tla-backend` `semantic_authority.rs`
/// `semantic_authority_run_level_refusal_before_image(&RunFixedFacts(f))`.
/// Recursive types are walked once each (`seen`); past `DEPTH_CAP` the answer is
/// `false`.
fn value_type_is_closed<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut FxHashSet<Ty<'tcx>>,
    depth: u32,
) -> bool {
    const DEPTH_CAP: u32 = 32;
    if depth > DEPTH_CAP
        || ty.has_param()
        || ty.has_aliases()
        || ty.references_error()
        || ty.has_infer()
        || ty.has_placeholders()
        || ty.has_escaping_bound_vars()
    {
        return false;
    }
    if !seen.insert(ty) {
        return true;
    }
    let mut closed = |t: Ty<'tcx>| value_type_is_closed(tcx, t, seen, depth + 1);
    match *ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => true,
        // A fn item names one body; its own arguments are that body's business —
        // but only a body THIS crate has, so it has a row here
        // ([`fn_item_has_local_body`]); its generic arguments are part of the value.
        ty::FnDef(def_id, args) => {
            fn_item_has_local_body(tcx, def_id) && args.skip_binder().types().all(closed)
        }
        ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Slice(inner) | ty::Array(inner, _) => {
            closed(inner)
        }
        ty::Tuple(elements) => elements.iter().all(closed),
        ty::Closure(_, args) => args.as_closure().upvar_tys().iter().all(closed),
        // The generic arguments too: `Vec<Box<dyn Tr>>` names its element type in a
        // `PhantomData` only, behind a non-generic raw buffer.
        ty::Adt(def, args) => {
            args.types().all(&mut closed)
                && def.all_fields().all(|field| closed(field.ty(tcx, args).skip_normalization()))
        }
        _ => false,
    }
}
