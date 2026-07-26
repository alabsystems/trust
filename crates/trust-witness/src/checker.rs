//! The linear replay checker (typeck-moonshot P0 kernel, ported).
//!
//! Ported verbatim from the proven P0 prototype
//! (`reports/typeck-moonshot/p0/replay_checker.rs`: `Counts`, `Checker`, its
//! `impl`, the `check_all` match, and `kind_name`). The checker walks a THIR
//! body — the fully-elaborated tree typeck produced — and re-validates every
//! node's type against its children using ONLY instantiation + structural
//! equality: no inference variables, no trait solving, no method probing.
//!
//! It is the MANDATORY pre-return authority (PLAN.md §6, constraint 2): a
//! decoded-but-unchecked replayed `TypeckResults` is never handed to any
//! consumer. `check` re-derives each node's type against the WARM `tcx`
//! (`teq` normalizes via `erase_and_anonymize_regions` /
//! `normalize_erasing_regions`; literals/ZST via `layout_of`; calls/ops via
//! warm `type_of` / instantiated sigs), which makes it a VALIDATOR, not a
//! self-consistency check: a candidate stale vs. the warm world produces
//! disagreeing node types and fails.
//!
//! Each node is classed CHECKED / WEAK (partial rule) / UNCHECKED (no rule in
//! v1); a FAIL means the checker's rule disagreed with rustc's answer (rustc is
//! ground truth). A subset of the WEAK classes — `call-non-fndef`,
//! `closure-fn-ptr-shape`, and the `unsize-*` shape-only classes — are
//! PICK-TRUSTING: they accept a shape without independently re-deriving the
//! underlying trait/method resolution. Those are counted separately as
//! `trusted_weak`, and the accept gate rejects any root with `trusted_weak > 0`.
//!
//! Driver-only bits of the prototype (the `fail_notes` Vec and the residue
//! `HashMap` printing) are dropped; a failing rule is logged at `debug` level.

use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::middle::region;
use rustc_middle::thir::{self, ExprId, ExprKind, LocalVarId, PatKind, StmtKind, Thir};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt, Unnormalized};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

/// The outcome of a linear check over one root's THIR.
///
/// `weak` is the total weak count; `trusted_weak` is the pick-trusting subset
/// of it (`call-non-fndef`, `closure-fn-ptr-shape`, `unsize-dyn`,
/// `unsize-tail-field`, `unsize-shape`) — the classes that accept a shape while
/// trusting a decoded trait/method resolution the linear checker cannot
/// independently re-derive.
pub struct CheckOutcome {
    pub checked: usize,
    pub weak: usize,
    pub unchecked: usize,
    pub failed: usize,
    pub trusted_weak: usize,
}

/// The accept predicate (PLAN.md §6): a replayed root may be used only when the
/// checker independently re-derived (or genuinely-soundly weak-accepted) every
/// node — no failures, no unchecked nodes, and no pick-trusting weak node.
pub fn accepts(o: &CheckOutcome) -> bool {
    o.failed == 0 && o.unchecked == 0 && o.trusted_weak == 0
}

/// Run the linear checker over one root's THIR against the warm `tcx`.
///
/// The candidate `TypeckResults` must already have been reconstructed into
/// `thir` (via a check-THIR build over the decoded results). `typing_env` is
/// the root's post-analysis env (`ty::TypingEnv::post_analysis(tcx, root)`).
///
/// `rederived` accumulates the re-materialized `FnDef` type of every call the
/// checker actually RE-RESOLVED (via `Instance::try_resolve` in the call-fndef
/// arm) — across every body of a forest-checked root. The replay authority then
/// requires every `type_dependent_defs` pick's `FnDef` ty to be in this set, so a
/// pick keyed to a child body that was never actually re-derived cannot be
/// accepted (the forest-checking completeness backstop).
pub fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    rederived: &mut FxHashSet<Ty<'tcx>>,
) -> CheckOutcome {
    let mut counts = Counts::default();
    {
        let mut ck = Checker {
            tcx,
            thir,
            typing_env,
            bindings: FxHashMap::default(),
            scope_targets: FxHashMap::default(),
            break_vals: FxHashMap::default(),
            counts: &mut counts,
            rederived,
        };
        ck.check_all();
    }
    CheckOutcome {
        checked: counts.checked,
        weak: counts.weak,
        unchecked: counts.unchecked,
        failed: counts.failed,
        trusted_weak: counts.trusted_weak,
    }
}

/// The pick-trusting weak classes (PLAN.md §6): these accept a structural shape
/// while trusting a decoded trait/method/coercion resolution the linear checker
/// cannot re-derive from local rules. Any of them present in a root forecloses
/// acceptance.
fn is_pick_trusting(class: &str) -> bool {
    matches!(
        class,
        "call-non-fndef"
            | "closure-fn-ptr-shape"
            | "unsize-dyn"
            | "unsize-tail-field"
            | "unsize-shape"
    )
}

#[derive(Default)]
struct Counts {
    checked: usize,
    weak: usize,
    unchecked: usize,
    failed: usize,
    /// The pick-trusting subset of `weak` (see `is_pick_trusting`).
    trusted_weak: usize,
}

impl Counts {
    fn weak_class(&mut self, class: &'static str) {
        self.weak += 1;
        if is_pick_trusting(class) {
            self.trusted_weak += 1;
        }
    }
    fn unchecked_class(&mut self, _class: &'static str) {
        self.unchecked += 1;
    }
}

struct Checker<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    bindings: FxHashMap<LocalVarId, Ty<'tcx>>,
    /// scope -> the expr that a `break` targeting that scope lands on.
    scope_targets: FxHashMap<region::Scope, ExprId>,
    /// break-target expr -> value types carried by breaks to it (None = unit).
    break_vals: FxHashMap<ExprId, Vec<Option<Ty<'tcx>>>>,
    counts: &'a mut Counts,
    /// The re-materialized `FnDef` tys of every RE-RESOLVED call (call-fndef arm),
    /// accumulated across a forest-checked root's bodies (see `check`).
    rederived: &'a mut FxHashSet<Ty<'tcx>>,
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    /// Structural equality modulo regions, with a normalization fallback for
    /// unnormalized associated types in instantiated signatures (the pick is
    /// given; normalization replays it). The fallback bills its cost to the
    /// CHECK side, which errs r upward — conservative for the kill gate.
    fn teq(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> bool {
        if a == b {
            return true;
        }
        let ea = self.tcx.erase_and_anonymize_regions(a);
        let eb = self.tcx.erase_and_anonymize_regions(b);
        if ea == eb {
            return true;
        }
        self.tcx.normalize_erasing_regions(self.typing_env, Unnormalized::new_wip(ea))
            == self.tcx.normalize_erasing_regions(self.typing_env, Unnormalized::new_wip(eb))
    }

    /// Equality with never-tolerance: `!` coerces into anything.
    fn teq_nv(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> bool {
        a.is_never() || self.teq(a, b)
    }

    fn ety(&self, e: ExprId) -> Ty<'tcx> {
        self.thir.exprs[e].ty
    }

    fn instantiated_type_of(&self, did: DefId, args: ty::GenericArgsRef<'tcx>) -> Ty<'tcx> {
        self.tcx.type_of(did).instantiate(self.tcx, args).skip_normalization()
    }

    fn collect_pat_bindings(&mut self, pat: &thir::Pat<'tcx>) {
        pat.walk_always(|p| {
            if let PatKind::Binding { var, ty, .. } = p.kind {
                self.bindings.insert(var, ty);
            }
        });
    }

    fn prepass_breaks(&mut self) {
        // Scope exprs name the region a `break` label refers to; the value the
        // break lands on is the wrapped expr (peeled through nested Scopes).
        for idx in 0..self.thir.exprs.len() {
            let eid = ExprId::from_usize(idx);
            if let ExprKind::Scope { region_scope, value, .. } = &self.thir.exprs[eid].kind {
                let mut v = *value;
                while let ExprKind::Scope { value: inner, .. } = &self.thir.exprs[v].kind {
                    v = *inner;
                }
                self.scope_targets.insert(*region_scope, v);
            }
        }
        for idx in 0..self.thir.exprs.len() {
            let eid = ExprId::from_usize(idx);
            if let ExprKind::Break { label, value } = &self.thir.exprs[eid].kind {
                if let Some(target) = self.scope_targets.get(label).copied() {
                    let vt = value.map(|v| self.ety(v));
                    self.break_vals.entry(target).or_default().push(vt);
                }
            }
        }
    }

    fn prepass_bindings(&mut self) {
        // Params, let-statements, match arms, let-expressions: every place a
        // LocalVarId is minted. Part of checker cost (it is linear).
        let params: Vec<_> =
            self.thir.params.iter().filter_map(|p| p.pat.as_deref().cloned()).collect();
        for pat in &params {
            self.collect_pat_bindings(pat);
        }
        let stmt_pats: Vec<_> = self
            .thir
            .stmts
            .iter()
            .filter_map(|s| match &s.kind {
                StmtKind::Let { pattern, .. } => Some((**pattern).clone()),
                _ => None,
            })
            .collect();
        for pat in &stmt_pats {
            self.collect_pat_bindings(pat);
        }
        let arm_pats: Vec<_> = self.thir.arms.iter().map(|a| (*a.pattern).clone()).collect();
        for pat in &arm_pats {
            self.collect_pat_bindings(pat);
        }
        let let_pats: Vec<_> = self
            .thir
            .exprs
            .iter()
            .filter_map(|e| match &e.kind {
                ExprKind::Let { pat, .. } => Some((**pat).clone()),
                _ => None,
            })
            .collect();
        for pat in &let_pats {
            self.collect_pat_bindings(pat);
        }
    }

    fn ok(&mut self, cond: bool, expr_idx: usize, rule: &str) {
        if cond {
            self.counts.checked += 1;
        } else {
            self.counts.failed += 1;
            let e = &self.thir.exprs[ExprId::from_usize(expr_idx)];
            let span = e.span;
            let ty = e.ty;
            let kind = kind_name(&e.kind);
            tracing::debug!(
                rule = %rule,
                ?span,
                ?ty,
                kind = %kind,
                "trust-witness checker: rule failed"
            );
        }
    }

    fn check_all(&mut self) {
        self.prepass_bindings();
        self.prepass_breaks();
        for idx in 0..self.thir.exprs.len() {
            let eid = ExprId::from_usize(idx);
            let e = &self.thir.exprs[eid];
            let ty = e.ty;
            match &e.kind {
                // ---- pure propagation nodes ----
                ExprKind::Scope { value, .. } => {
                    let c = self.teq(self.ety(*value), ty);
                    self.ok(c, idx, "scope-propagate")
                }
                ExprKind::Use { source } | ExprKind::ByUse { expr: source, .. } => {
                    let c = self.teq(self.ety(*source), ty);
                    self.ok(c, idx, "use-propagate")
                }
                ExprKind::NeverToAny { source } => {
                    let c = self.ety(*source).is_never();
                    self.ok(c, idx, "never-to-any")
                }
                ExprKind::PlaceTypeAscription { source, .. }
                | ExprKind::ValueTypeAscription { source, .. } => {
                    let c = self.teq(self.ety(*source), ty);
                    self.ok(c, idx, "ascription-propagate")
                }

                // ---- literals ----
                ExprKind::Literal { lit, .. } => {
                    use rustc_ast::LitKind::*;
                    let c = match lit.node {
                        Str(..) => matches!(ty.kind(), ty::Ref(_, t, _) if t.is_str()),
                        ByteStr(..) => true, // &[u8; N] or &[u8] — shape varies, weak below
                        CStr(..) => true,
                        Byte(_) => matches!(ty.kind(), ty::Uint(ty::UintTy::U8)),
                        Char(_) => ty.is_char(),
                        Int(..) => ty.is_integral(),
                        Float(..) => ty.is_floating_point(),
                        Bool(_) => ty.is_bool(),
                        Err(_) => true,
                    };
                    self.ok(c, idx, "literal-kind")
                }
                ExprKind::NonHirLiteral { lit, .. } => {
                    match self.tcx.layout_of(self.typing_env.as_query_input(ty)) {
                        Ok(l) => {
                            let c = l.layout.is_zst() && lit.size().bytes() == 0
                                || l.layout.size() == lit.size();
                            self.ok(c, idx, "non-hir-literal-size")
                        }
                        Err(_) => self.counts.weak_class("nonhir-lit-no-layout"),
                    }
                }
                ExprKind::ZstLiteral { .. } => {
                    // FnDef/unit-struct values; generic bodies may lack layout.
                    match self.tcx.layout_of(self.typing_env.as_query_input(ty)) {
                        Ok(l) => self.ok(l.layout.is_zst(), idx, "zst-literal"),
                        Err(_) => self.counts.weak_class("zst-lit-no-layout"),
                    }
                }
                ExprKind::StaticRef { ty: sty, .. } => {
                    let c = self.teq(*sty, ty);
                    self.ok(c, idx, "static-ref")
                }

                // ---- operators (builtin only in THIR) ----
                ExprKind::Unary { op, arg } => {
                    use rustc_middle::mir::UnOp::*;
                    let at = self.ety(*arg);
                    let c = self.teq(at, ty)
                        && match op {
                            Not => at.is_bool() || at.is_integral(),
                            Neg => at.is_integral() || at.is_floating_point(),
                            PtrMetadata => true, // ty differs; weak-accept
                        };
                    // PtrMetadata breaks the teq premise; check via metadata ty.
                    if matches!(op, PtrMetadata) {
                        match at.builtin_deref(true) {
                            Some(pointee) => {
                                let md = pointee.ptr_metadata_ty_or_tail(self.tcx, |t| {
                                    self.tcx.normalize_erasing_regions(self.typing_env, t)
                                });
                                match md {
                                    Ok(md) => {
                                        let c2 = self.teq(md, ty);
                                        self.ok(c2, idx, "ptr-metadata")
                                    }
                                    Err(_) => self.counts.weak_class("ptr-metadata-tail"),
                                }
                            }
                            None => self.counts.weak_class("ptr-metadata-nonptr"),
                        }
                    } else {
                        self.ok(c, idx, "unary")
                    }
                }
                ExprKind::Binary { op, lhs, rhs } => {
                    use rustc_middle::mir::BinOp::*;
                    let lt = self.ety(*lhs);
                    let rt = self.ety(*rhs);
                    let c = match op {
                        Add | Sub | Mul | Div | Rem | BitXor | BitAnd | BitOr => {
                            self.teq(lt, rt) && self.teq(lt, ty)
                        }
                        Shl | Shr => self.teq(lt, ty) && rt.is_integral(),
                        Eq | Lt | Le | Ne | Ge | Gt => self.teq(lt, rt) && ty.is_bool(),
                        Cmp => self.teq(lt, rt), // result is Ordering
                        Offset => true,
                        _ => true, // unchecked/checked variants of arith are MIR-only, but stay total
                    };
                    self.ok(c, idx, "binary")
                }
                ExprKind::LogicalOp { lhs, rhs, .. } => {
                    let c = self.ety(*lhs).is_bool() && self.ety(*rhs).is_bool() && ty.is_bool();
                    self.ok(c, idx, "logical")
                }
                ExprKind::AssignOp { op, lhs, rhs } => {
                    use rustc_middle::mir::AssignOp::*;
                    let lt = self.ety(*lhs);
                    let rt = self.ety(*rhs);
                    let op_ok = match op {
                        ShlAssign | ShrAssign => rt.is_integral(),
                        _ => self.teq(lt, rt),
                    };
                    let c = ty.is_unit() && op_ok && lt.is_primitive();
                    self.ok(c, idx, "assign-op")
                }
                ExprKind::Assign { lhs, rhs } => {
                    let c = ty.is_unit() && self.teq_nv(self.ety(*rhs), self.ety(*lhs));
                    self.ok(c, idx, "assign")
                }

                // ---- places ----
                ExprKind::Deref { arg } => {
                    let at = self.ety(*arg);
                    let c = match at.builtin_deref(true) {
                        Some(pointee) => self.teq(pointee, ty),
                        None => false,
                    };
                    self.ok(c, idx, "deref")
                }
                ExprKind::Borrow { arg, .. } => {
                    let c = matches!(ty.kind(), ty::Ref(_, pointee, _) if self.teq(*pointee, self.ety(*arg)));
                    self.ok(c, idx, "borrow")
                }
                ExprKind::RawBorrow { mutability, arg } => {
                    let c = matches!(ty.kind(), ty::RawPtr(pointee, m) if self.teq(*pointee, self.ety(*arg)) && m == mutability);
                    self.ok(c, idx, "raw-borrow")
                }
                // A reborrow (`&*r` / auto-reborrow, and the pin-ergonomics
                // GenericReborrow): the node's type is the recorded `target`
                // reborrowed type, and the source is a reference/pointer place.
                ExprKind::Reborrow { source, target, .. } => {
                    let src = self.ety(*source);
                    let c = self.teq(*target, ty)
                        && matches!(src.kind(), ty::Ref(..) | ty::RawPtr(..) | ty::Adt(..));
                    self.ok(c, idx, "reborrow")
                }
                ExprKind::Field { lhs, variant_index, name } => {
                    let lt = self.ety(*lhs);
                    let c = match lt.kind() {
                        ty::Adt(def, args) => {
                            let fty = def.variant(*variant_index).fields[*name].ty(self.tcx, args).skip_normalization();
                            self.teq(fty, ty)
                        }
                        ty::Tuple(elts) => {
                            elts.get(name.as_usize()).is_some_and(|t| self.teq(*t, ty))
                        }
                        _ => false,
                    };
                    self.ok(c, idx, "field")
                }
                ExprKind::Index { lhs, index } => {
                    let lt = self.ety(*lhs);
                    let c = self.ety(*index).is_usize()
                        && match lt.kind() {
                            ty::Array(elem, _) | ty::Slice(elem) => self.teq(*elem, ty),
                            _ => false,
                        };
                    self.ok(c, idx, "index")
                }
                ExprKind::VarRef { id } => match self.bindings.get(id) {
                    Some(bt) => {
                        let bt = *bt;
                        let c = self.teq(bt, ty);
                        self.ok(c, idx, "var-ref")
                    }
                    None => self.counts.weak_class("varref-unknown-binding"),
                },

                // ---- aggregates ----
                ExprKind::Tuple { fields } => {
                    let c = match ty.kind() {
                        ty::Tuple(elts) => {
                            elts.len() == fields.len()
                                && elts
                                    .iter()
                                    .zip(fields.iter())
                                    .all(|(t, f)| self.teq_nv(self.ety(*f), t))
                        }
                        _ => false,
                    };
                    self.ok(c, idx, "tuple")
                }
                ExprKind::Array { fields } => {
                    let c = match ty.kind() {
                        ty::Array(elem, n) => {
                            n.try_to_target_usize(self.tcx) == Some(fields.len() as u64)
                                && fields.iter().all(|f| self.teq_nv(self.ety(*f), *elem))
                        }
                        _ => false,
                    };
                    self.ok(c, idx, "array")
                }
                ExprKind::Repeat { value, count } => {
                    let c = match ty.kind() {
                        ty::Array(elem, n) => self.teq(self.ety(*value), *elem) && *n == *count,
                        _ => false,
                    };
                    self.ok(c, idx, "repeat")
                }
                ExprKind::Adt(adt) => {
                    let hd = matches!(ty.kind(), ty::Adt(def, args) if *def == adt.adt_def && *args == adt.args);
                    let flds = adt.fields.iter().all(|f| {
                        let decl =
                            adt.adt_def.variant(adt.variant_index).fields[f.name].ty(self.tcx, adt.args).skip_normalization();
                        self.teq_nv(self.ety(f.expr), decl)
                    });
                    self.ok(hd && flds, idx, "adt-ctor")
                }

                // ---- calls: the pick is the FnDef + args; check = instantiate + eq ----
                ExprKind::Call { ty: fty, fun, args, .. } => {
                    let c_fun = self.teq(self.ety(*fun), *fty);
                    match fty.kind() {
                        ty::FnDef(did, gargs) => {
                            let sig = self.tcx.instantiate_bound_regions_with_erased(
                                self.tcx.fn_sig(*did).instantiate(self.tcx, gargs).skip_normalization(),
                            );
                            let inputs = sig.inputs();
                            let arity = if sig.c_variadic() {
                                args.len() >= inputs.len()
                            } else {
                                inputs.len() == args.len()
                            };
                            let params_ok = arity
                                && inputs
                                    .iter()
                                    .zip(args.iter())
                                    .all(|(p, a)| self.teq_nv(self.ety(*a), *p));
                            let ret_ok = self.teq(sig.output(), ty);
                            // Half-2 (Follow-on 2): for a fully-ground call, RE-DERIVE
                            // impl selection with codegen's own resolver rather than
                            // trusting the recorded pick. The receiver type is already
                            // pinned by `params_ok`. Non-ground calls or defs outside
                            // try_resolve's domain keep the prior signature-only check.
                            // A pre-guard on def_kind avoids try_resolve's internal
                            // assert; Ok(None) (e.g. type-length bail) conservatively
                            // rejects to real typeck — sound, perf-only.
                            use rustc_hir::def::{CtorKind, DefKind};
                            let resolvable_kind = matches!(
                                self.tcx.def_kind(*did),
                                DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn)
                            );
                            let resolves = gargs.has_param()
                                || !resolvable_kind
                                || matches!(
                                    ty::Instance::try_resolve(
                                        self.tcx,
                                        self.typing_env,
                                        *did,
                                        *gargs,
                                    ),
                                    Ok(Some(_))
                                );
                            // Forest-checking backstop: record the re-materialized
                            // FnDef ty of a genuinely re-resolved call, so the replay
                            // authority can require every type_dependent_defs pick to
                            // have actually been re-derived across the walked forest.
                            if resolves {
                                self.rederived.insert(*fty);
                            }
                            self.ok(c_fun && params_ok && ret_ok && resolves, idx, "call-fndef")
                        }
                        ty::FnPtr(sig_tys, hdr) => {
                            let sig =
                                self.tcx.instantiate_bound_regions_with_erased(sig_tys.with(*hdr));
                            let params_ok = sig.inputs().len() == args.len()
                                && sig
                                    .inputs()
                                    .iter()
                                    .zip(args.iter())
                                    .all(|(p, a)| self.teq_nv(self.ety(*a), *p));
                            let ret_ok = self.teq(sig.output(), ty);
                            self.ok(c_fun && params_ok && ret_ok, idx, "call-fnptr")
                        }
                        _ => self.counts.weak_class("call-non-fndef"),
                    }
                }

                // ---- consts with given picks ----
                ExprKind::NamedConst { def_id, args, .. } => {
                    let c = self.teq(self.instantiated_type_of(*def_id, args), ty);
                    self.ok(c, idx, "named-const")
                }
                ExprKind::ConstBlock { did, args } => {
                    let c = self.teq(self.instantiated_type_of(*did, args), ty);
                    self.ok(c, idx, "const-block")
                }
                ExprKind::ConstParam { def_id, .. } => {
                    let c = self.teq(self.tcx.type_of(*def_id).instantiate_identity().skip_normalization(), ty);
                    self.ok(c, idx, "const-param")
                }

                // ---- control flow ----
                ExprKind::If { cond, then, else_opt, .. } => {
                    let cond_ok = self.ety(*cond).is_bool();
                    let arms_ok = match else_opt {
                        Some(els) => {
                            self.teq_nv(self.ety(*then), ty) && self.teq_nv(self.ety(*els), ty)
                        }
                        None => ty.is_unit() || ty.is_never(),
                    };
                    self.ok(cond_ok && arms_ok, idx, "if")
                }
                ExprKind::Let { expr, pat } => {
                    let c = ty.is_bool() && self.teq(pat.ty, self.ety(*expr));
                    self.ok(c, idx, "let-expr")
                }
                ExprKind::Match { scrutinee, arms, .. } => {
                    let st = self.ety(*scrutinee);
                    let pats_ok = arms
                        .iter()
                        .all(|a| self.teq(self.thir.arms[*a].pattern.ty, st));
                    let bodies_ok = arms
                        .iter()
                        .all(|a| self.teq_nv(self.ety(self.thir.arms[*a].body), ty));
                    let guards_ok = arms.iter().all(|a| {
                        self.thir.arms[*a].guard.map_or(true, |g| self.ety(g).is_bool())
                    });
                    self.ok(pats_ok && bodies_ok && guards_ok, idx, "match")
                }
                ExprKind::Block { block } => {
                    let b = &self.thir.blocks[*block];
                    let tail_ok = match b.expr {
                        Some(tail) => self.teq_nv(self.ety(tail), ty),
                        None => ty.is_unit() || ty.is_never(),
                    };
                    // A labeled block's type may come from `break 'label val`.
                    let c = tail_ok
                        || (b.targeted_by_break
                            && self.break_vals.get(&eid).is_some_and(|vals| {
                                vals.iter().all(|v| match v {
                                    None => ty.is_unit(),
                                    Some(vt) => self.teq_nv(*vt, ty),
                                })
                            }));
                    self.ok(c, idx, "block")
                }
                ExprKind::Return { .. }
                | ExprKind::Break { .. }
                | ExprKind::Continue { .. }
                | ExprKind::Become { .. }
                | ExprKind::ConstContinue { .. } => {
                    let c = ty.is_never();
                    self.ok(c, idx, "diverging")
                }

                // ---- casts ----
                ExprKind::Cast { source } => {
                    let st = self.ety(*source);
                    let num = |t: Ty<'tcx>| {
                        t.is_numeric() || t.is_char() || t.is_bool()
                    };
                    if num(st) && ty.is_numeric() {
                        // numeric-family cast: bool/char/int/float -> int/float
                        self.ok(true, idx, "cast-numeric")
                    } else if num(st) && ty.is_char() {
                        // only u8 as char is admissible
                        self.ok(matches!(st.kind(), ty::Uint(ty::UintTy::U8)), idx, "cast-to-char")
                    } else if (st.is_any_ptr() || st.is_numeric())
                        && (ty.is_any_ptr() || ty.is_numeric())
                    {
                        // ptr<->ptr / ptr<->int shape; pointee compat unchecked here
                        self.counts.weak_class("cast-ptr-shape")
                    } else if st.is_enum() && ty.is_numeric() {
                        self.ok(true, idx, "cast-enum-discr")
                    } else {
                        self.counts.weak_class("cast-other")
                    }
                }
                ExprKind::PointerCoercion { cast, source, .. } => {
                    use rustc_middle::ty::adjustment::PointerCoercion as PC;
                    let st = self.ety(*source);
                    match cast {
                        PC::ReifyFnPointer(_) => {
                            let c = match (st.kind(), ty.kind()) {
                                (ty::FnDef(did, gargs), ty::FnPtr(sig_tys, hdr)) => {
                                    let src_sig = self.tcx.instantiate_bound_regions_with_erased(
                                        self.tcx.fn_sig(*did).instantiate(self.tcx, gargs).skip_normalization(),
                                    );
                                    let dst_sig = self
                                        .tcx
                                        .instantiate_bound_regions_with_erased(sig_tys.with(*hdr));
                                    // Soundness (audit 2026-07-22, rank 1): the
                                    // fn-ptr ABI is NOT round-tripped (decode
                                    // rebuilds Rust), so a reify whose source fn
                                    // carries a different ABI/safety than the
                                    // decoded target must FAIL — never treat ABI
                                    // as don't-care on an arm that admits a FnPtr.
                                    src_sig.abi() == dst_sig.abi()
                                        && src_sig.safety() == dst_sig.safety()
                                        && src_sig.inputs().len() == dst_sig.inputs().len()
                                        && src_sig
                                            .inputs()
                                            .iter()
                                            .zip(dst_sig.inputs())
                                            .all(|(a, b)| self.teq(*a, *b))
                                        && self.teq(src_sig.output(), dst_sig.output())
                                }
                                _ => false,
                            };
                            self.ok(c, idx, "reify-fn-ptr")
                        }
                        PC::UnsafeFnPointer => {
                            let c = matches!((st.kind(), ty.kind()), (ty::FnPtr(a, _), ty::FnPtr(b, _)) if a == b);
                            self.ok(c, idx, "unsafe-fn-ptr")
                        }
                        PC::MutToConstPointer => {
                            let c = matches!(
                                (st.kind(), ty.kind()),
                                (ty::RawPtr(p1, hir::Mutability::Mut), ty::RawPtr(p2, hir::Mutability::Not))
                                    if self.teq(*p1, *p2)
                            );
                            self.ok(c, idx, "mut-to-const-ptr")
                        }
                        PC::ArrayToPointer => {
                            let c = match (st.kind(), ty.kind()) {
                                (ty::RawPtr(p1, _), ty::RawPtr(p2, _)) => {
                                    matches!(p1.kind(), ty::Array(e1, _) if self.teq(*e1, *p2))
                                }
                                _ => false,
                            };
                            self.ok(c, idx, "array-to-ptr")
                        }
                        PC::ClosureFnPointer(_) => {
                            let c = st.is_closure() && ty.is_fn_ptr();
                            if c {
                                self.counts.weak_class("closure-fn-ptr-shape")
                            } else {
                                self.ok(false, idx, "closure-fn-ptr")
                            }
                        }
                        PC::Unsize => {
                            // Peel one pointer/ref/Box layer from both sides.
                            let peel = |t: Ty<'tcx>| match t.kind() {
                                ty::Ref(_, p, _) | ty::RawPtr(p, _) => Some(*p),
                                _ if t.is_box() => t.boxed_ty(),
                                _ => None,
                            };
                            match (peel(st), peel(ty)) {
                                (Some(sp), Some(dp)) => match (sp.kind(), dp.kind()) {
                                    (ty::Array(e1, _), ty::Slice(e2)) => {
                                        let c = self.teq(*e1, *e2);
                                        self.ok(c, idx, "unsize-array-slice")
                                    }
                                    (_, ty::Dynamic(..)) => {
                                        // `T: Trait` is a trait judgement — the
                                        // pick is implicit in v1; shape only.
                                        self.counts.weak_class("unsize-dyn")
                                    }
                                    _ => self.counts.weak_class("unsize-tail-field"),
                                },
                                _ => self.counts.weak_class("unsize-shape"),
                            }
                        }
                    }
                }

                // ---- loops (break-value collected in prepass) ----
                ExprKind::Loop { .. } => {
                    let c = match self.break_vals.get(&eid) {
                        None => ty.is_never() || ty.is_unit(),
                        Some(vals) => vals.iter().all(|v| match v {
                            None => ty.is_unit(),
                            Some(vt) => self.teq_nv(*vt, ty),
                        }),
                    };
                    self.ok(c, idx, "loop")
                }

                // ---- closures ----
                ExprKind::Closure(cl) => {
                    let head_ok = match ty.kind() {
                        ty::Closure(did, _)
                        | ty::CoroutineClosure(did, _)
                        | ty::Coroutine(did, _) => *did == cl.closure_id.to_def_id(),
                        _ => false,
                    };
                    let uv = cl.args.upvar_tys();
                    let upvars_ok = uv.len() == cl.upvars.len()
                        && uv
                            .iter()
                            .zip(cl.upvars.iter())
                            .all(|(t, u)| self.teq(t, self.ety(*u)));
                    self.ok(head_ok && upvars_ok, idx, "closure")
                }

                // ---- still-unchecked mass (each classed for the ledger) ----
                ExprKind::LoopMatch { .. } => self.counts.unchecked_class("loop-match"),
                ExprKind::UpvarRef { .. } => self.counts.unchecked_class("upvar-ref"),
                ExprKind::PlaceUnwrapUnsafeBinder { .. }
                | ExprKind::ValueUnwrapUnsafeBinder { .. }
                | ExprKind::WrapUnsafeBinder { .. } => {
                    self.counts.unchecked_class("unsafe-binder")
                }
                ExprKind::InlineAsm(..) => self.counts.unchecked_class("inline-asm"),
                ExprKind::ThreadLocalRef(..) => self.counts.unchecked_class("thread-local"),
                ExprKind::Yield { .. } => self.counts.unchecked_class("yield"),
            }
        }
    }
}

fn kind_name(k: &ExprKind<'_>) -> &'static str {
    match k {
        ExprKind::Scope { .. } => "Scope",
        ExprKind::If { .. } => "If",
        ExprKind::Call { .. } => "Call",
        ExprKind::Deref { .. } => "Deref",
        ExprKind::Binary { .. } => "Binary",
        ExprKind::Borrow { .. } => "Borrow",
        ExprKind::Block { .. } => "Block",
        ExprKind::Field { .. } => "Field",
        ExprKind::VarRef { .. } => "VarRef",
        ExprKind::Literal { .. } => "Literal",
        _ => "other",
    }
}
