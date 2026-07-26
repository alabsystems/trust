//! Utilities for manipulating and extracting information from `rustc_ast::ast`.
//!
//! - The `eq_foobar` functions test for semantic equality but ignores `NodeId`s and `Span`s.

#![allow(clippy::wildcard_imports, clippy::enum_glob_use)]

use crate::{both, over};
use rustc_ast::visit::{self, Visitor};
use rustc_ast::{self as ast, HasAttrs, *};
use rustc_span::sym;
use rustc_span::symbol::Ident;
use std::mem;

pub mod ident_iter;
pub use ident_iter::IdentIter;

pub fn is_useless_with_eq_exprs(kind: BinOpKind) -> bool {
    use BinOpKind::*;
    matches!(
        kind,
        Sub | Div | Eq | Lt | Le | Gt | Ge | Ne | And | Or | BitXor | BitAnd | BitOr
    )
}

/// Checks if each element in the first slice is contained within the latter as per `eq_fn`.
pub fn unordered_over<X, Y>(left: &[X], right: &[Y], mut eq_fn: impl FnMut(&X, &Y) -> bool) -> bool {
    left.len() == right.len() && left.iter().all(|l| right.iter().any(|r| eq_fn(l, r)))
}

pub fn eq_id(l: Ident, r: Ident) -> bool {
    l.name == r.name
}

fn item_kind_has_authored_verifier_source(kind: &ItemKind) -> bool {
    matches!(kind, ItemKind::Fn(function) if function.contract.is_some()) || matches!(kind, ItemKind::CleanIsland(_))
}

#[derive(Default)]
struct AuthoredVerifierSourceFinder {
    found: bool,
}

impl<'ast> Visitor<'ast> for AuthoredVerifierSourceFinder {
    fn visit_contract(&mut self, _contract: &'ast FnContract) {
        // Free functions are caught by `visit_item` below, but contracts on
        // trait, impl, and foreign functions are reached through
        // `visit_fn`/`visit_contract` instead. Treat every function context
        // alike: all of these payloads are span-only verifier source that
        // `pprust` cannot reconstruct.
        self.found = true;
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if matches!(expr.kind, ExprKind::While(_, _, _, Some(_))) {
            self.found = true;
            return;
        }
        visit::walk_expr(self, expr);
    }

    fn visit_item(&mut self, item: &'ast Item) {
        if item_kind_has_authored_verifier_source(&item.kind) {
            self.found = true;
            return;
        }
        visit::walk_item(self, item);
    }
}

/// Returns whether pretty-printing or replacing `pat` could cross authored
/// Trust verifier source embedded in one of its expression/item subtrees.
///
/// Span-only contract payloads and Clean islands cannot be reconstructed by
/// `pprust`, so AST source suggestions must conservatively leave such patterns
/// untouched.
pub fn pat_contains_authored_contract(pat: &Pat) -> bool {
    let mut finder = AuthoredVerifierSourceFinder::default();
    finder.visit_pat(pat);
    finder.found
}

pub fn eq_pat(l: &Pat, r: &Pat) -> bool {
    use PatKind::*;
    match (&l.kind, &r.kind) {
        (Missing, _) | (_, Missing) => unreachable!(),
        (Paren(l), _) => eq_pat(l, r),
        (_, Paren(r)) => eq_pat(l, r),
        (Wild, Wild) | (Rest, Rest) => true,
        (Expr(l), Expr(r)) => eq_expr(l, r),
        (Ident(b1, i1, s1), Ident(b2, i2, s2)) => {
            b1 == b2 && eq_id(*i1, *i2) && both(s1.as_deref(), s2.as_deref(), eq_pat)
        },
        (Range(lf, lt, le), Range(rf, rt, re)) => {
            eq_expr_opt(lf.as_deref(), rf.as_deref())
                && eq_expr_opt(lt.as_deref(), rt.as_deref())
                && eq_range_end(le.node, re.node)
        },
        (Box(l), Box(r)) => eq_pat(l, r),
        (Ref(l, l_pin, l_mut), Ref(r, r_pin, r_mut)) => l_pin == r_pin && l_mut == r_mut && eq_pat(l, r),
        (Tuple(l), Tuple(r)) | (Slice(l), Slice(r)) => over(l, r, eq_pat),
        (Path(lq, lp), Path(rq, rp)) => both(lq.as_deref(), rq.as_deref(), eq_qself) && eq_path(lp, rp),
        (TupleStruct(lqself, lp, lfs), TupleStruct(rqself, rp, rfs)) => {
            eq_maybe_qself(lqself.as_deref(), rqself.as_deref()) && eq_path(lp, rp) && over(lfs, rfs, eq_pat)
        },
        (Struct(lqself, lp, lfs, lr), Struct(rqself, rp, rfs, rr)) => {
            lr == rr
                && eq_maybe_qself(lqself.as_deref(), rqself.as_deref())
                && eq_path(lp, rp)
                && unordered_over(lfs, rfs, eq_field_pat)
        },
        (Or(ls), Or(rs)) => unordered_over(ls, rs, eq_pat),
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_range_end(l: RangeEnd, r: RangeEnd) -> bool {
    match (l, r) {
        (RangeEnd::Excluded, RangeEnd::Excluded) => true,
        (RangeEnd::Included(l), RangeEnd::Included(r)) => {
            matches!(l, RangeSyntax::DotDotEq) == matches!(r, RangeSyntax::DotDotEq)
        },
        _ => false,
    }
}

pub fn eq_field_pat(l: &PatField, r: &PatField) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && eq_pat(&l.pat, &r.pat)
        && over(&l.attrs, &r.attrs, eq_attr)
}

fn eq_qself(l: &QSelf, r: &QSelf) -> bool {
    l.position == r.position && eq_ty(&l.ty, &r.ty)
}

pub fn eq_maybe_qself(l: Option<&QSelf>, r: Option<&QSelf>) -> bool {
    match (l, r) {
        (Some(l), Some(r)) => eq_qself(l, r),
        (None, None) => true,
        _ => false,
    }
}

pub fn eq_path(l: &Path, r: &Path) -> bool {
    over(&l.segments, &r.segments, eq_path_seg)
}

fn eq_path_seg(l: &PathSegment, r: &PathSegment) -> bool {
    eq_id(l.ident, r.ident) && both(l.args.as_ref(), r.args.as_ref(), |l, r| eq_generic_args(l, r))
}

fn eq_generic_args(l: &GenericArgs, r: &GenericArgs) -> bool {
    match (l, r) {
        (AngleBracketed(l), AngleBracketed(r)) => over(&l.args, &r.args, eq_angle_arg),
        (Parenthesized(l), Parenthesized(r)) => {
            over(&l.inputs, &r.inputs, |l, r| eq_ty(l, r)) && eq_fn_ret_ty(&l.output, &r.output)
        },
        _ => false,
    }
}

fn eq_angle_arg(l: &AngleBracketedArg, r: &AngleBracketedArg) -> bool {
    match (l, r) {
        (AngleBracketedArg::Arg(l), AngleBracketedArg::Arg(r)) => eq_generic_arg(l, r),
        (AngleBracketedArg::Constraint(l), AngleBracketedArg::Constraint(r)) => eq_assoc_item_constraint(l, r),
        _ => false,
    }
}

fn eq_generic_arg(l: &GenericArg, r: &GenericArg) -> bool {
    match (l, r) {
        (GenericArg::Lifetime(l), GenericArg::Lifetime(r)) => eq_id(l.ident, r.ident),
        (GenericArg::Type(l), GenericArg::Type(r)) => eq_ty(l, r),
        (GenericArg::Const(l), GenericArg::Const(r)) => eq_expr(&l.value, &r.value),
        _ => false,
    }
}

fn eq_expr_opt(l: Option<&Expr>, r: Option<&Expr>) -> bool {
    both(l, r, eq_expr)
}

fn eq_struct_rest(l: &StructRest, r: &StructRest) -> bool {
    match (l, r) {
        (StructRest::Base(lb), StructRest::Base(rb)) => eq_expr(lb, rb),
        (StructRest::Rest(_), StructRest::Rest(_)) | (StructRest::None, StructRest::None) => true,
        _ => false,
    }
}

#[expect(clippy::too_many_lines, reason = "big match statement")]
fn eq_expr(l: &Expr, r: &Expr) -> bool {
    use ExprKind::*;
    if !over(&l.attrs, &r.attrs, eq_attr) {
        return false;
    }
    match (&l.kind, &r.kind) {
        (Paren(l), _) => eq_expr(l, r),
        (_, Paren(r)) => eq_expr(l, r),
        (Err(_), Err(_)) => true,
        (Dummy, _) | (_, Dummy) => unreachable!("comparing `ExprKind::Dummy`"),
        (Try(l), Try(r)) | (Await(l, _), Await(r, _)) => eq_expr(l, r),
        (Array(l), Array(r)) => over(l, r, |l, r| eq_expr(l, r)),
        (Tup(l), Tup(r)) => over(l, r, |l, r| eq_expr(l, r)),
        (Repeat(le, ls), Repeat(re, rs)) => eq_expr(le, re) && eq_expr(&ls.value, &rs.value),
        (Call(lc, la), Call(rc, ra)) => eq_expr(lc, rc) && over(la, ra, |l, r| eq_expr(l, r)),
        (
            MethodCall(box ast::MethodCall {
                seg: ls,
                receiver: lr,
                args: la,
                ..
            }),
            MethodCall(box ast::MethodCall {
                seg: rs,
                receiver: rr,
                args: ra,
                ..
            }),
        ) => eq_path_seg(ls, rs) && eq_expr(lr, rr) && over(la, ra, |l, r| eq_expr(l, r)),
        (Binary(lo, ll, lr), Binary(ro, rl, rr)) => lo.node == ro.node && eq_expr(ll, rl) && eq_expr(lr, rr),
        (Unary(lo, l), Unary(ro, r)) => mem::discriminant(lo) == mem::discriminant(ro) && eq_expr(l, r),
        (Lit(l), Lit(r)) => l == r,
        (Cast(l, lt), Cast(r, rt)) | (Type(l, lt), Type(r, rt)) => eq_expr(l, r) && eq_ty(lt, rt),
        (Let(lp, le, _, _), Let(rp, re, _, _)) => eq_pat(lp, rp) && eq_expr(le, re),
        (If(lc, lt, le), If(rc, rt, re)) => {
            eq_expr(lc, rc) && eq_block(lt, rt) && eq_expr_opt(le.as_deref(), re.as_deref())
        },
        (While(lc, lt, ll, l_contract), While(rc, rt, rl, r_contract)) => {
            eq_label(ll.as_ref(), rl.as_ref())
                && eq_expr(lc, rc)
                && eq_block(lt, rt)
                && eq_loop_contract(l_contract.as_deref(), r_contract.as_deref())
        },
        (
            ForLoop {
                pat: lp,
                iter: li,
                body: lt,
                label: ll,
                kind: lk,
            },
            ForLoop {
                pat: rp,
                iter: ri,
                body: rt,
                label: rl,
                kind: rk,
            },
        ) => eq_label(ll.as_ref(), rl.as_ref()) && eq_pat(lp, rp) && eq_expr(li, ri) && eq_block(lt, rt) && lk == rk,
        (Loop(lt, ll, _), Loop(rt, rl, _)) => eq_label(ll.as_ref(), rl.as_ref()) && eq_block(lt, rt),
        (Block(lb, ll), Block(rb, rl)) => eq_label(ll.as_ref(), rl.as_ref()) && eq_block(lb, rb),
        (TryBlock(lb, lt), TryBlock(rb, rt)) => eq_block(lb, rb) && both(lt.as_deref(), rt.as_deref(), eq_ty),
        (Yield(l), Yield(r)) => eq_expr_opt(l.expr().map(Box::as_ref), r.expr().map(Box::as_ref)) && l.same_kind(r),
        (Ret(l), Ret(r)) => eq_expr_opt(l.as_deref(), r.as_deref()),
        (Break(ll, le), Break(rl, re)) => {
            eq_label(ll.as_ref(), rl.as_ref()) && eq_expr_opt(le.as_deref(), re.as_deref())
        },
        (Continue(ll), Continue(rl)) => eq_label(ll.as_ref(), rl.as_ref()),
        (Assign(l1, l2, _), Assign(r1, r2, _)) | (Index(l1, l2, _), Index(r1, r2, _)) => {
            eq_expr(l1, r1) && eq_expr(l2, r2)
        },
        (AssignOp(lo, lp, lv), AssignOp(ro, rp, rv)) => lo.node == ro.node && eq_expr(lp, rp) && eq_expr(lv, rv),
        (Field(lp, lf), Field(rp, rf)) => eq_id(*lf, *rf) && eq_expr(lp, rp),
        (Match(ls, la, lkind), Match(rs, ra, rkind)) => (lkind == rkind) && eq_expr(ls, rs) && over(la, ra, eq_arm),
        (
            Closure(box ast::Closure {
                binder: lb,
                capture_clause: lc,
                coroutine_kind: la,
                movability: lm,
                fn_decl: lf,
                body: le,
                ..
            }),
            Closure(box ast::Closure {
                binder: rb,
                capture_clause: rc,
                coroutine_kind: ra,
                movability: rm,
                fn_decl: rf,
                body: re,
                ..
            }),
        ) => {
            eq_closure_binder(lb, rb)
                && lc == rc
                && eq_coroutine_kind(*la, *ra)
                && lm == rm
                && eq_fn_decl(lf, rf)
                && eq_expr(le, re)
        },
        (Gen(lc, lb, lk, _), Gen(rc, rb, rk, _)) => lc == rc && eq_block(lb, rb) && lk == rk,
        (Range(lf, lt, ll), Range(rf, rt, rl)) => {
            ll == rl && eq_expr_opt(lf.as_deref(), rf.as_deref()) && eq_expr_opt(lt.as_deref(), rt.as_deref())
        },
        (AddrOf(lbk, lm, le), AddrOf(rbk, rm, re)) => lbk == rbk && lm == rm && eq_expr(le, re),
        (Path(lq, lp), Path(rq, rp)) => both(lq.as_deref(), rq.as_deref(), eq_qself) && eq_path(lp, rp),
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        (Struct(lse), Struct(rse)) => {
            eq_maybe_qself(lse.qself.as_deref(), rse.qself.as_deref())
                && eq_path(&lse.path, &rse.path)
                && eq_struct_rest(&lse.rest, &rse.rest)
                && unordered_over(&lse.fields, &rse.fields, eq_field)
        },
        _ => false,
    }
}

fn eq_coroutine_kind(a: Option<CoroutineKind>, b: Option<CoroutineKind>) -> bool {
    matches!(
        (a, b),
        (Some(CoroutineKind::Async { .. }), Some(CoroutineKind::Async { .. }))
            | (Some(CoroutineKind::Gen { .. }), Some(CoroutineKind::Gen { .. }))
            | (
                Some(CoroutineKind::AsyncGen { .. }),
                Some(CoroutineKind::AsyncGen { .. })
            )
            | (None, None)
    )
}

fn eq_field(l: &ExprField, r: &ExprField) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && eq_expr(&l.expr, &r.expr)
        && over(&l.attrs, &r.attrs, eq_attr)
}

fn eq_arm(l: &Arm, r: &Arm) -> bool {
    l.is_placeholder == r.is_placeholder
        && eq_pat(&l.pat, &r.pat)
        && eq_expr_opt(l.body.as_deref(), r.body.as_deref())
        && eq_expr_opt(l.guard.as_deref().map(|g| &g.cond), r.guard.as_deref().map(|g| &g.cond))
        && over(&l.attrs, &r.attrs, eq_attr)
}

fn eq_label(l: Option<&Label>, r: Option<&Label>) -> bool {
    both(l, r, |l, r| eq_id(l.ident, r.ident))
}

fn eq_loop_contract(l: Option<&LoopContract>, r: Option<&LoopContract>) -> bool {
    both(l, r, |l, r| {
        over(&l.clauses, &r.clauses, |l, r| {
            l.kind == r.kind && l.keyword_span == r.keyword_span && eq_trust_native_clause(&l.clause, &r.clause)
        })
    })
}

// Trust: a native clause is verifier vocabulary, so its predicate never reaches
// the Rust expression comparisons above. Span equality alone is not enough to
// recognize a clone: expansion may stamp one call-site span on every clause it
// emits, and two clauses that differ only in their payload would then compare
// equal — enough for a code-sharing suggestion to collapse two branches that
// specify different things. The parser's token-rendered payload is the faithful
// spelling under expansion, so require it too.
fn eq_trust_native_clause(l: &TrustNativeClause, r: &TrustNativeClause) -> bool {
    l.predicate == r.predicate && l.payload == r.payload && l.citation == r.citation
}

fn eq_trust_native_clauses(l: &[TrustNativeClause], r: &[TrustNativeClause]) -> bool {
    over(l, r, eq_trust_native_clause)
}

fn eq_block(l: &Block, r: &Block) -> bool {
    l.rules == r.rules && over(&l.stmts, &r.stmts, eq_stmt)
}

fn eq_stmt(l: &Stmt, r: &Stmt) -> bool {
    use StmtKind::*;
    match (&l.kind, &r.kind) {
        (Let(l), Let(r)) => {
            eq_pat(&l.pat, &r.pat)
                && both(l.ty.as_ref(), r.ty.as_ref(), |l, r| eq_ty(l, r))
                && eq_local_kind(&l.kind, &r.kind)
                && over(&l.attrs, &r.attrs, eq_attr)
        },
        (Item(l), Item(r)) => eq_item(l, r, eq_item_kind),
        (Expr(l), Expr(r)) | (Semi(l), Semi(r)) => eq_expr(l, r),
        (Empty, Empty) => true,
        (MacCall(l), MacCall(r)) => {
            l.style == r.style && eq_mac_call(&l.mac, &r.mac) && over(&l.attrs, &r.attrs, eq_attr)
        },
        _ => false,
    }
}

fn eq_local_kind(l: &LocalKind, r: &LocalKind) -> bool {
    use LocalKind::*;
    match (l, r) {
        (Decl, Decl) => true,
        (Init(l), Init(r)) => eq_expr(l, r),
        (InitElse(li, le), InitElse(ri, re)) => eq_expr(li, ri) && eq_block(le, re),
        _ => false,
    }
}

fn eq_item<K>(l: &Item<K>, r: &Item<K>, mut eq_kind: impl FnMut(&K, &K) -> bool) -> bool {
    over(&l.attrs, &r.attrs, eq_attr) && eq_vis(&l.vis, &r.vis) && eq_kind(&l.kind, &r.kind)
}

#[expect(clippy::too_many_lines, reason = "big match statement")]
fn eq_item_kind(l: &ItemKind, r: &ItemKind) -> bool {
    use ItemKind::*;
    match (l, r) {
        (ExternCrate(ls, li), ExternCrate(rs, ri)) => ls == rs && eq_id(*li, *ri),
        (Use(l), Use(r)) => eq_use_tree(l, r),
        (
            Static(box StaticItem {
                ident: li,
                ty: lt,
                mutability: lm,
                expr: le,
                safety: ls,
                define_opaque: _,
                eii_impls: _,
            }),
            Static(box StaticItem {
                ident: ri,
                ty: rt,
                mutability: rm,
                expr: re,
                safety: rs,
                define_opaque: _,
                eii_impls: _,
            }),
        ) => eq_id(*li, *ri) && lm == rm && ls == rs && eq_ty(lt, rt) && eq_expr_opt(le.as_deref(), re.as_deref()),
        (
            Const(box ConstItem {
                defaultness: ld,
                ident: li,
                generics: lg,
                ty: lt,
                rhs_kind: lb,
                define_opaque: _,
            }),
            Const(box ConstItem {
                defaultness: rd,
                ident: ri,
                generics: rg,
                ty: rt,
                rhs_kind: rb,
                define_opaque: _,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && eq_ty(lt, rt)
                && both(Some(lb), Some(rb), eq_const_item_rhs)
        },
        (
            Fn(box ast::Fn {
                defaultness: ld,
                sig: lf,
                ident: li,
                generics: lg,
                contract: lc,
                body: lb,
                define_opaque: _,
                eii_impls: _,
            }),
            Fn(box ast::Fn {
                defaultness: rd,
                sig: rf,
                ident: ri,
                generics: rg,
                contract: rc,
                body: rb,
                define_opaque: _,
                eii_impls: _,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_fn_sig(lf, rf)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && eq_opt_fn_contract(lc, rc)
                && both(lb.as_ref(), rb.as_ref(), |l, r| eq_block(l, r))
        },
        (Mod(ls, li, lmk), Mod(rs, ri, rmk)) => {
            ls == rs
                && eq_id(*li, *ri)
                && match (lmk, rmk) {
                    (ModKind::Loaded(litems, linline, _), ModKind::Loaded(ritems, rinline, _)) => {
                        linline == rinline && over(litems, ritems, |l, r| eq_item(l, r, eq_item_kind))
                    },
                    (ModKind::Unloaded, ModKind::Unloaded) => true,
                    _ => false,
                }
        },
        (ForeignMod(l), ForeignMod(r)) => {
            both(l.abi.as_ref(), r.abi.as_ref(), eq_str_lit)
                && over(&l.items, &r.items, |l, r| eq_item(l, r, eq_foreign_item_kind))
        },
        (
            TyAlias(box ast::TyAlias {
                defaultness: ld,
                generics: lg,
                bounds: lb,
                ty: lt,
                ..
            }),
            TyAlias(box ast::TyAlias {
                defaultness: rd,
                generics: rg,
                bounds: rb,
                ty: rt,
                ..
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_generics(lg, rg)
                && over(lb, rb, eq_generic_bound)
                && both(lt.as_ref(), rt.as_ref(), |l, r| eq_ty(l, r))
        },
        (Enum(li, lg, le), Enum(ri, rg, re)) => {
            eq_id(*li, *ri) && eq_generics(lg, rg) && over(&le.variants, &re.variants, eq_variant)
        },
        (Struct(li, lg, lv), Struct(ri, rg, rv)) | (Union(li, lg, lv), Union(ri, rg, rv)) => {
            eq_id(*li, *ri) && eq_generics(lg, rg) && eq_variant_data(lv, rv)
        },
        (
            Trait(box ast::Trait {
                impl_restriction: liprt,
                constness: lc,
                is_auto: la,
                safety: lu,
                ident: li,
                generics: lg,
                bounds: lb,
                items: lis,
            }),
            Trait(box ast::Trait {
                impl_restriction: riprt,
                constness: rc,
                is_auto: ra,
                safety: ru,
                ident: ri,
                generics: rg,
                bounds: rb,
                items: ris,
            }),
        ) => {
            eq_impl_restriction(liprt, riprt)
                && matches!(lc, ast::Const::No) == matches!(rc, ast::Const::No)
                && la == ra
                && matches!(lu, Safety::Default) == matches!(ru, Safety::Default)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && over(lb, rb, eq_generic_bound)
                && over(lis, ris, |l, r| eq_item(l, r, eq_assoc_item_kind))
        },
        (
            TraitAlias(box ast::TraitAlias {
                ident: li,
                generics: lg,
                bounds: lb,
                constness: lc,
            }),
            TraitAlias(box ast::TraitAlias {
                ident: ri,
                generics: rg,
                bounds: rb,
                constness: rc,
            }),
        ) => {
            matches!(lc, ast::Const::No) == matches!(rc, ast::Const::No)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && over(lb, rb, eq_generic_bound)
        },
        (
            Impl(ast::Impl {
                generics: lg,
                of_trait: lot,
                self_ty: lst,
                items: li,
                constness: lc,
            }),
            Impl(ast::Impl {
                generics: rg,
                of_trait: rot,
                self_ty: rst,
                items: ri,
                constness: rc,
            }),
        ) => {
            eq_generics(lg, rg)
                && both(lot.as_deref(), rot.as_deref(), |l, r| {
                    matches!(l.safety, Safety::Default) == matches!(r.safety, Safety::Default)
                        && matches!(l.polarity, ImplPolarity::Positive) == matches!(r.polarity, ImplPolarity::Positive)
                        && eq_defaultness(l.defaultness, r.defaultness)
                        && matches!(lc, ast::Const::No) == matches!(rc, ast::Const::No)
                        && eq_path(&l.trait_ref.path, &r.trait_ref.path)
                })
                && eq_ty(lst, rst)
                && over(li, ri, |l, r| eq_item(l, r, eq_assoc_item_kind))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        (MacroDef(li, ld), MacroDef(ri, rd)) => {
            eq_id(*li, *ri) && ld.macro_rules == rd.macro_rules && eq_delim_args(&ld.body, &rd.body)
        },
        _ => false,
    }
}

fn eq_foreign_item_kind(l: &ForeignItemKind, r: &ForeignItemKind) -> bool {
    use ForeignItemKind::*;
    match (l, r) {
        (
            Static(box StaticItem {
                ident: li,
                ty: lt,
                mutability: lm,
                expr: le,
                safety: ls,
                define_opaque: _,
                eii_impls: _,
            }),
            Static(box StaticItem {
                ident: ri,
                ty: rt,
                mutability: rm,
                expr: re,
                safety: rs,
                define_opaque: _,
                eii_impls: _,
            }),
        ) => eq_id(*li, *ri) && eq_ty(lt, rt) && lm == rm && eq_expr_opt(le.as_deref(), re.as_deref()) && ls == rs,
        (
            Fn(box ast::Fn {
                defaultness: ld,
                sig: lf,
                ident: li,
                generics: lg,
                contract: lc,
                body: lb,
                define_opaque: _,
                eii_impls: _,
            }),
            Fn(box ast::Fn {
                defaultness: rd,
                sig: rf,
                ident: ri,
                generics: rg,
                contract: rc,
                body: rb,
                define_opaque: _,
                eii_impls: _,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_fn_sig(lf, rf)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && eq_opt_fn_contract(lc, rc)
                && both(lb.as_ref(), rb.as_ref(), |l, r| eq_block(l, r))
        },
        (
            TyAlias(box ast::TyAlias {
                defaultness: ld,
                ident: li,
                generics: lg,
                after_where_clause: lw,
                bounds: lb,
                ty: lt,
            }),
            TyAlias(box ast::TyAlias {
                defaultness: rd,
                ident: ri,
                generics: rg,
                after_where_clause: rw,
                bounds: rb,
                ty: rt,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && over(&lw.predicates, &rw.predicates, eq_where_predicate)
                && over(lb, rb, eq_generic_bound)
                && both(lt.as_ref(), rt.as_ref(), |l, r| eq_ty(l, r))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_assoc_item_kind(l: &AssocItemKind, r: &AssocItemKind) -> bool {
    use AssocItemKind::*;
    match (l, r) {
        (
            Const(box ConstItem {
                defaultness: ld,
                ident: li,
                generics: lg,
                ty: lt,
                rhs_kind: lb,
                define_opaque: _,
            }),
            Const(box ConstItem {
                defaultness: rd,
                ident: ri,
                generics: rg,
                ty: rt,
                rhs_kind: rb,
                define_opaque: _,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && eq_ty(lt, rt)
                && both(Some(lb), Some(rb), eq_const_item_rhs)
        },
        (
            Fn(box ast::Fn {
                defaultness: ld,
                sig: lf,
                ident: li,
                generics: lg,
                contract: lc,
                body: lb,
                define_opaque: _,
                eii_impls: _,
            }),
            Fn(box ast::Fn {
                defaultness: rd,
                sig: rf,
                ident: ri,
                generics: rg,
                contract: rc,
                body: rb,
                define_opaque: _,
                eii_impls: _,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_fn_sig(lf, rf)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && eq_opt_fn_contract(lc, rc)
                && both(lb.as_ref(), rb.as_ref(), |l, r| eq_block(l, r))
        },
        (
            Type(box TyAlias {
                defaultness: ld,
                ident: li,
                generics: lg,
                after_where_clause: lw,
                bounds: lb,
                ty: lt,
            }),
            Type(box TyAlias {
                defaultness: rd,
                ident: ri,
                generics: rg,
                after_where_clause: rw,
                bounds: rb,
                ty: rt,
            }),
        ) => {
            eq_defaultness(*ld, *rd)
                && eq_id(*li, *ri)
                && eq_generics(lg, rg)
                && over(&lw.predicates, &rw.predicates, eq_where_predicate)
                && over(lb, rb, eq_generic_bound)
                && both(lt.as_ref(), rt.as_ref(), |l, r| eq_ty(l, r))
        },
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_variant(l: &Variant, r: &Variant) -> bool {
    l.is_placeholder == r.is_placeholder
        && over(&l.attrs, &r.attrs, eq_attr)
        && eq_vis(&l.vis, &r.vis)
        && eq_id(l.ident, r.ident)
        && eq_variant_data(&l.data, &r.data)
        && both(l.disr_expr.as_ref(), r.disr_expr.as_ref(), |l, r| {
            eq_expr(&l.value, &r.value)
        })
}

fn eq_variant_data(l: &VariantData, r: &VariantData) -> bool {
    use VariantData::*;
    match (l, r) {
        (Unit(_), Unit(_)) => true,
        (Struct { fields: l, .. }, Struct { fields: r, .. }) | (Tuple(l, _), Tuple(r, _)) => {
            over(l, r, eq_struct_field)
        },
        _ => false,
    }
}

fn eq_struct_field(l: &FieldDef, r: &FieldDef) -> bool {
    l.is_placeholder == r.is_placeholder
        && over(&l.attrs, &r.attrs, eq_attr)
        && eq_vis(&l.vis, &r.vis)
        && eq_mut_restriction(&l.mut_restriction, &r.mut_restriction)
        && both(l.ident.as_ref(), r.ident.as_ref(), |l, r| eq_id(*l, *r))
        && eq_ty(&l.ty, &r.ty)
}

fn eq_fn_sig(l: &FnSig, r: &FnSig) -> bool {
    eq_fn_decl(&l.decl, &r.decl) && eq_fn_header(&l.header, &r.header)
}

fn eq_opt_coroutine_kind(l: Option<CoroutineKind>, r: Option<CoroutineKind>) -> bool {
    matches!(
        (l, r),
        (Some(CoroutineKind::Async { .. }), Some(CoroutineKind::Async { .. }))
            | (Some(CoroutineKind::Gen { .. }), Some(CoroutineKind::Gen { .. }))
            | (
                Some(CoroutineKind::AsyncGen { .. }),
                Some(CoroutineKind::AsyncGen { .. })
            )
            | (None, None)
    )
}

fn eq_fn_header(l: &FnHeader, r: &FnHeader) -> bool {
    matches!(l.safety, Safety::Default) == matches!(r.safety, Safety::Default)
        && eq_opt_coroutine_kind(l.coroutine_kind, r.coroutine_kind)
        && matches!(l.constness, Const::No) == matches!(r.constness, Const::No)
        && eq_ext(&l.ext, &r.ext)
}

#[expect(clippy::ref_option, reason = "This is the type how it is stored in the AST")]
fn eq_opt_fn_contract(l: &Option<Box<FnContract>>, r: &Option<Box<FnContract>>) -> bool {
    match (l, r) {
        (Some(l), Some(r)) => {
            over(&l.declarations, &r.declarations, eq_stmt)
                && eq_expr_opt(l.requires.as_deref(), r.requires.as_deref())
                && eq_expr_opt(l.ensures.as_deref(), r.ensures.as_deref())
                && over(&l.requires_clauses, &r.requires_clauses, |l, r| eq_expr(l, r))
                && over(&l.ensures_clauses, &r.ensures_clauses, |l, r| eq_expr(l, r))
                // The opaque lane is span-only: exact span equality safely
                // recognizes an AST clone, and independently authored clauses
                // are conservatively different because nothing here can read
                // the attribute payload those spans point at. The native lane
                // does carry its payload; see `eq_trust_native_clause`.
                && l.trust_opaque_requires == r.trust_opaque_requires
                && l.trust_opaque_ensures == r.trust_opaque_ensures
                && eq_trust_native_clauses(
                    &l.trust_native_requires,
                    &r.trust_native_requires,
                )
                && eq_trust_native_clauses(
                    &l.trust_native_ensures,
                    &r.trust_native_ensures,
                )
                && l.clause_order == r.clause_order
        },
        (None, None) => true,
        (Some(_), None) | (None, Some(_)) => false,
    }
}

fn eq_generics(l: &Generics, r: &Generics) -> bool {
    over(&l.params, &r.params, eq_generic_param)
        && over(&l.where_clause.predicates, &r.where_clause.predicates, |l, r| {
            eq_where_predicate(l, r)
        })
}

fn eq_where_predicate(l: &WherePredicate, r: &WherePredicate) -> bool {
    use WherePredicateKind::*;
    over(&l.attrs, &r.attrs, eq_attr)
        && match (&l.kind, &r.kind) {
            (BoundPredicate(l), BoundPredicate(r)) => {
                over(&l.bound_generic_params, &r.bound_generic_params, |l, r| {
                    eq_generic_param(l, r)
                }) && eq_ty(&l.bounded_ty, &r.bounded_ty)
                    && over(&l.bounds, &r.bounds, eq_generic_bound)
            },
            (RegionPredicate(l), RegionPredicate(r)) => {
                eq_id(l.lifetime.ident, r.lifetime.ident) && over(&l.bounds, &r.bounds, eq_generic_bound)
            },
            _ => false,
        }
}

fn eq_use_tree(l: &UseTree, r: &UseTree) -> bool {
    eq_path(&l.prefix, &r.prefix) && eq_use_tree_kind(&l.kind, &r.kind)
}

fn eq_anon_const(l: &AnonConst, r: &AnonConst) -> bool {
    eq_expr(&l.value, &r.value)
}

fn eq_const_item_rhs(l: &ConstItemRhsKind, r: &ConstItemRhsKind) -> bool {
    use ConstItemRhsKind::*;
    match (l, r) {
        (TypeConst { rhs: Some(l) }, TypeConst { rhs: Some(r) }) => eq_anon_const(l, r),
        (TypeConst { rhs: None }, TypeConst { rhs: None }) | (Body { rhs: None }, Body { rhs: None }) => true,
        (Body { rhs: Some(l) }, Body { rhs: Some(r) }) => eq_expr(l, r),
        (TypeConst { rhs: Some(..) }, TypeConst { rhs: None })
        | (TypeConst { rhs: None }, TypeConst { rhs: Some(..) })
        | (Body { rhs: None }, Body { rhs: Some(..) })
        | (Body { rhs: Some(..) }, Body { rhs: None })
        | (TypeConst { .. }, Body { .. })
        | (Body { .. }, TypeConst { .. }) => false,
    }
}

fn eq_use_tree_kind(l: &UseTreeKind, r: &UseTreeKind) -> bool {
    use UseTreeKind::*;
    match (l, r) {
        (Glob(_), Glob(_)) => true,
        (Simple(l), Simple(r)) => both(l.as_ref(), r.as_ref(), |l, r| eq_id(*l, *r)),
        (Nested { items: l, .. }, Nested { items: r, .. }) => over(l, r, |(l, _), (r, _)| eq_use_tree(l, r)),
        _ => false,
    }
}

fn eq_defaultness(l: Defaultness, r: Defaultness) -> bool {
    matches!(
        (l, r),
        (Defaultness::Implicit, Defaultness::Implicit)
            | (Defaultness::Default(_), Defaultness::Default(_))
            | (Defaultness::Final(_), Defaultness::Final(_))
    )
}

fn eq_vis(l: &Visibility, r: &Visibility) -> bool {
    use VisibilityKind::*;
    match (&l.kind, &r.kind) {
        (Public, Public) | (Inherited, Inherited) => true,
        (Restricted { path: l, .. }, Restricted { path: r, .. }) => eq_path(l, r),
        _ => false,
    }
}

fn eq_impl_restriction(l: &ImplRestriction, r: &ImplRestriction) -> bool {
    eq_restriction_kind(&l.kind, &r.kind)
}

pub fn eq_mut_restriction(l: &MutRestriction, r: &MutRestriction) -> bool {
    eq_restriction_kind(&l.kind, &r.kind)
}

fn eq_restriction_kind(l: &RestrictionKind, r: &RestrictionKind) -> bool {
    match (l, r) {
        (RestrictionKind::Unrestricted, RestrictionKind::Unrestricted) => true,
        (
            RestrictionKind::Restricted {
                path: l_path,
                shorthand: l_short,
                id: _,
            },
            RestrictionKind::Restricted {
                path: r_path,
                shorthand: r_short,
                id: _,
            },
        ) => l_short == r_short && eq_path(l_path, r_path),
        _ => false,
    }
}

fn eq_fn_decl(l: &FnDecl, r: &FnDecl) -> bool {
    eq_fn_ret_ty(&l.output, &r.output)
        && over(&l.inputs, &r.inputs, |l, r| {
            l.is_placeholder == r.is_placeholder
                && eq_pat(&l.pat, &r.pat)
                && eq_ty(&l.ty, &r.ty)
                && over(&l.attrs, &r.attrs, eq_attr)
        })
}

fn eq_closure_binder(l: &ClosureBinder, r: &ClosureBinder) -> bool {
    match (l, r) {
        (ClosureBinder::NotPresent, ClosureBinder::NotPresent) => true,
        (ClosureBinder::For { generic_params: lp, .. }, ClosureBinder::For { generic_params: rp, .. }) => {
            lp.len() == rp.len() && std::iter::zip(lp.iter(), rp.iter()).all(|(l, r)| eq_generic_param(l, r))
        },
        _ => false,
    }
}

fn eq_fn_ret_ty(l: &FnRetTy, r: &FnRetTy) -> bool {
    match (l, r) {
        (FnRetTy::Default(_), FnRetTy::Default(_)) => true,
        (FnRetTy::Ty(l), FnRetTy::Ty(r)) => eq_ty(l, r),
        _ => false,
    }
}

fn eq_ty(l: &Ty, r: &Ty) -> bool {
    use TyKind::*;
    match (&l.kind, &r.kind) {
        (Paren(l), _) => eq_ty(l, r),
        (_, Paren(r)) => eq_ty(l, r),
        (Never, Never) | (Infer, Infer) | (ImplicitSelf, ImplicitSelf) | (Err(_), Err(_)) | (CVarArgs, CVarArgs) => {
            true
        },
        (Slice(l), Slice(r)) => eq_ty(l, r),
        (Array(le, ls), Array(re, rs)) => eq_ty(le, re) && eq_expr(&ls.value, &rs.value),
        (Ptr(l), Ptr(r)) => l.mutbl == r.mutbl && eq_ty(&l.ty, &r.ty),
        (Ref(ll, l), Ref(rl, r)) => {
            both(ll.as_ref(), rl.as_ref(), |l, r| eq_id(l.ident, r.ident)) && l.mutbl == r.mutbl && eq_ty(&l.ty, &r.ty)
        },
        (PinnedRef(ll, l), PinnedRef(rl, r)) => {
            both(ll.as_ref(), rl.as_ref(), |l, r| eq_id(l.ident, r.ident)) && l.mutbl == r.mutbl && eq_ty(&l.ty, &r.ty)
        },
        (FnPtr(l), FnPtr(r)) => {
            l.safety == r.safety
                && eq_ext(&l.ext, &r.ext)
                && over(&l.generic_params, &r.generic_params, eq_generic_param)
                && eq_fn_decl(&l.decl, &r.decl)
        },
        (Tup(l), Tup(r)) => over(l, r, |l, r| eq_ty(l, r)),
        (Path(lq, lp), Path(rq, rp)) => both(lq.as_deref(), rq.as_deref(), eq_qself) && eq_path(lp, rp),
        (TraitObject(lg, ls), TraitObject(rg, rs)) => ls == rs && over(lg, rg, eq_generic_bound),
        (ImplTrait(_, lg), ImplTrait(_, rg)) => over(lg, rg, eq_generic_bound),
        (MacCall(l), MacCall(r)) => eq_mac_call(l, r),
        _ => false,
    }
}

fn eq_ext(l: &Extern, r: &Extern) -> bool {
    use Extern::*;
    match (l, r) {
        (None, None) | (Implicit(_), Implicit(_)) => true,
        (Explicit(l, _), Explicit(r, _)) => eq_str_lit(l, r),
        _ => false,
    }
}

fn eq_str_lit(l: &StrLit, r: &StrLit) -> bool {
    l.style == r.style && l.symbol == r.symbol && l.suffix == r.suffix
}

fn eq_poly_ref_trait(l: &PolyTraitRef, r: &PolyTraitRef) -> bool {
    l.modifiers == r.modifiers
        && eq_path(&l.trait_ref.path, &r.trait_ref.path)
        && over(&l.bound_generic_params, &r.bound_generic_params, |l, r| {
            eq_generic_param(l, r)
        })
}

fn eq_generic_param(l: &GenericParam, r: &GenericParam) -> bool {
    use GenericParamKind::*;
    l.is_placeholder == r.is_placeholder
        && eq_id(l.ident, r.ident)
        && over(&l.bounds, &r.bounds, eq_generic_bound)
        && match (&l.kind, &r.kind) {
            (Lifetime, Lifetime) => true,
            (Type { default: l }, Type { default: r }) => both(l.as_ref(), r.as_ref(), |l, r| eq_ty(l, r)),
            (
                Const {
                    ty: lt,
                    default: ld,
                    span: _,
                },
                Const {
                    ty: rt,
                    default: rd,
                    span: _,
                },
            ) => eq_ty(lt, rt) && both(ld.as_ref(), rd.as_ref(), eq_anon_const),
            _ => false,
        }
        && over(&l.attrs, &r.attrs, eq_attr)
}

fn eq_generic_bound(l: &GenericBound, r: &GenericBound) -> bool {
    use GenericBound::*;
    match (l, r) {
        (Trait(ptr1), Trait(ptr2)) => eq_poly_ref_trait(ptr1, ptr2),
        (Outlives(l), Outlives(r)) => eq_id(l.ident, r.ident),
        _ => false,
    }
}

fn eq_term(l: &Term, r: &Term) -> bool {
    match (l, r) {
        (Term::Ty(l), Term::Ty(r)) => eq_ty(l, r),
        (Term::Const(l), Term::Const(r)) => eq_anon_const(l, r),
        _ => false,
    }
}

fn eq_assoc_item_constraint(l: &AssocItemConstraint, r: &AssocItemConstraint) -> bool {
    use AssocItemConstraintKind::*;
    eq_id(l.ident, r.ident)
        && match (&l.kind, &r.kind) {
            (Equality { term: l }, Equality { term: r }) => eq_term(l, r),
            (Bound { bounds: l }, Bound { bounds: r }) => over(l, r, eq_generic_bound),
            _ => false,
        }
}

fn eq_mac_call(l: &MacCall, r: &MacCall) -> bool {
    eq_path(&l.path, &r.path) && eq_delim_args(&l.args, &r.args)
}

fn eq_attr(l: &Attribute, r: &Attribute) -> bool {
    use AttrKind::*;
    l.style == r.style
        && match (&l.kind, &r.kind) {
            (DocComment(l1, l2), DocComment(r1, r2)) => l1 == r1 && l2 == r2,
            (Normal(l), Normal(r)) => {
                eq_path(&l.item.path, &r.item.path) && eq_attr_item_kind(&l.item.args, &r.item.args)
            },
            _ => false,
        }
}

fn eq_attr_item_kind(l: &AttrItemKind, r: &AttrItemKind) -> bool {
    match (l, r) {
        (AttrItemKind::Unparsed(l), AttrItemKind::Unparsed(r)) => eq_attr_args(l, r),
        (
            AttrItemKind::Parsed(EarlyParsedAttribute::CfgTrace(l)),
            AttrItemKind::Parsed(EarlyParsedAttribute::CfgTrace(r)),
        ) => l.is_equivalent_to(r),
        (
            AttrItemKind::Parsed(EarlyParsedAttribute::CfgAttrTrace),
            AttrItemKind::Parsed(EarlyParsedAttribute::CfgAttrTrace),
        ) => {
            // `CfgAttrTrace` deliberately erases its original arguments.
            // There is not enough information here to prove two attributes
            // equivalent, so fail closed instead of panicking or guessing.
            false
        },
        _ => false,
    }
}

fn eq_attr_args(l: &AttrArgs, r: &AttrArgs) -> bool {
    use AttrArgs::*;
    match (l, r) {
        (Empty, Empty) => true,
        (Delimited(la), Delimited(ra)) => eq_delim_args(la, ra),
        (Eq { eq_span: _, expr: le }, Eq { eq_span: _, expr: re }) => eq_expr(le, re),
        _ => false,
    }
}

fn eq_delim_args(l: &DelimArgs, r: &DelimArgs) -> bool {
    l.delim == r.delim
        && l.tokens.len() == r.tokens.len()
        && l.tokens.iter().zip(r.tokens.iter()).all(|(a, b)| a.eq_unspanned(b))
}

/// Checks whether `#[cfg(test)]` is directly applied to `item`.
pub fn is_cfg_test(item: &impl HasAttrs) -> bool {
    item.attrs().iter().any(|attr| {
        if attr.has_name(sym::cfg)
            && let Some(item_list) = attr.meta_item_list()
            && item_list.iter().any(|item| item.has_name(sym::test))
        {
            true
        } else {
            false
        }
    })
}

#[cfg(test)]
mod tests {
    use super::{
        AuthoredVerifierSourceFinder, eq_attr_item_kind, eq_loop_contract, eq_opt_fn_contract,
        item_kind_has_authored_verifier_source, pat_contains_authored_contract,
    };
    use rustc_ast::DUMMY_NODE_ID;
    use rustc_ast::ast::{
        AttrItemKind, Block, BlockCheckMode, EarlyParsedAttribute, Expr, ExprKind, FnContract, FnContractClauseKind,
        FnContractClauseLane, FnContractClauseMarker, ItemKind, LoopClause, LoopClauseKind, LoopContract, Pat, PatKind,
        Stmt, StmtKind, TrustCitation, TrustNativeClause,
    };
    use rustc_ast::attr::data_structures::CfgEntry;
    use rustc_ast::visit::Visitor;
    use rustc_span::{BytePos, DUMMY_SP, Span, Symbol, create_default_session_globals_then};

    fn citation(name: &str, span: Span) -> TrustCitation {
        TrustCitation {
            name: Symbol::intern(name),
            span,
        }
    }

    /// A native clause carrying the authored spelling the parser would record.
    /// Interning it needs session globals, so every caller runs inside them.
    fn native_clause(payload: &str, predicate: Span, citation: Option<TrustCitation>) -> TrustNativeClause {
        TrustNativeClause {
            predicate,
            payload: Symbol::intern(payload),
            citation,
        }
    }

    fn assert_fn_contract_lane_is_semantic(mutate: impl FnOnce(&mut FnContract)) {
        let left = Some(Box::new(FnContract::default()));
        let mut right = Some(Box::new(FnContract::default()));
        assert!(eq_opt_fn_contract(&left, &right));
        mutate(right.as_deref_mut().unwrap());
        assert!(!eq_opt_fn_contract(&left, &right));
    }

    #[test]
    fn fn_contract_equality_covers_every_contract_lane() {
        create_default_session_globals_then(|| {
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.requires = Some(Box::new(Expr::dummy()));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.ensures = Some(Box::new(Expr::dummy()));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.declarations.push(Stmt {
                    id: DUMMY_NODE_ID,
                    kind: StmtKind::Empty,
                    span: DUMMY_SP,
                });
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.requires_clauses.push(Box::new(Expr::dummy()));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.ensures_clauses.push(Box::new(Expr::dummy()));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.trust_opaque_requires.push(DUMMY_SP);
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.trust_opaque_ensures.push(DUMMY_SP);
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract
                    .trust_native_requires
                    .push(native_clause("x > 0", DUMMY_SP, None));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract
                    .trust_native_ensures
                    .push(native_clause("result > 0", DUMMY_SP, None));
            });
            assert_fn_contract_lane_is_semantic(|contract| {
                contract.clause_order.push(FnContractClauseMarker {
                    ordinal: 0,
                    kind: FnContractClauseKind::Requires,
                    lane: FnContractClauseLane::Typed,
                    lane_index: 0,
                });
            });
        });
    }

    #[test]
    fn fn_contract_equality_detects_citation_only_mutation() {
        create_default_session_globals_then(|| {
            let mut left_contract = FnContract::default();
            left_contract
                .trust_native_ensures
                .push(native_clause("result > 0", DUMMY_SP, None));
            let left = Some(Box::new(left_contract));
            let mut right = left.clone();
            right.as_deref_mut().unwrap().trust_native_ensures[0].citation =
                Some(citation("Lemma.bound", Span::with_root_ctxt(BytePos(1), BytePos(2))));

            assert!(!eq_opt_fn_contract(&left, &right));
        });
    }

    #[test]
    fn fn_contract_equality_detects_canonical_citation_name_mutation() {
        create_default_session_globals_then(|| {
            let citation_span = Span::with_root_ctxt(BytePos(1), BytePos(2));
            let mut left_contract = FnContract::default();
            left_contract.trust_native_ensures.push(native_clause(
                "result > 0",
                DUMMY_SP,
                Some(citation("Lemma.one", citation_span)),
            ));
            let left = Some(Box::new(left_contract));
            let mut right = left.clone();
            right.as_deref_mut().unwrap().trust_native_ensures[0]
                .citation
                .as_mut()
                .unwrap()
                .name = Symbol::intern("Lemma.two");

            assert!(!eq_opt_fn_contract(&left, &right));
        });
    }

    #[test]
    fn fn_contract_equality_detects_citation_source_span_mutation() {
        create_default_session_globals_then(|| {
            let mut left_contract = FnContract::default();
            left_contract.trust_native_ensures.push(native_clause(
                "result > 0",
                DUMMY_SP,
                Some(citation("Lemma.same", DUMMY_SP)),
            ));
            let left = Some(Box::new(left_contract));
            let mut right = left.clone();
            right.as_deref_mut().unwrap().trust_native_ensures[0]
                .citation
                .as_mut()
                .unwrap()
                .span = Span::with_root_ctxt(BytePos(1), BytePos(2));

            assert!(!eq_opt_fn_contract(&left, &right));
        });
    }

    #[test]
    fn loop_contract_equality_requires_exact_authored_metadata() {
        create_default_session_globals_then(|| {
            let mut left = LoopContract::default();
            left.clauses.push(LoopClause {
                kind: LoopClauseKind::Invariant,
                keyword_span: DUMMY_SP,
                clause: native_clause("i < n", DUMMY_SP, None),
            });
            let mut right = left.clone();
            assert!(eq_loop_contract(Some(&left), Some(&right)));

            right.clauses[0].clause.predicate = Span::with_root_ctxt(BytePos(1), BytePos(2));
            assert!(!eq_loop_contract(Some(&left), Some(&right)));
            assert!(!eq_loop_contract(Some(&left), None));
        });
    }

    /// Expansion can stamp one call-site span on every clause it emits, so a
    /// pair that differs only in its authored spelling must still compare
    /// unequal — otherwise a code-sharing suggestion could merge two loops that
    /// specify different things.
    #[test]
    fn loop_contract_equality_detects_payload_only_mutation() {
        create_default_session_globals_then(|| {
            let mut left = LoopContract::default();
            left.clauses.push(LoopClause {
                kind: LoopClauseKind::Invariant,
                keyword_span: DUMMY_SP,
                clause: native_clause("i < n", DUMMY_SP, None),
            });
            let mut right = left.clone();
            assert!(eq_loop_contract(Some(&left), Some(&right)));

            right.clauses[0].clause = native_clause("i <= n", DUMMY_SP, None);
            assert!(!eq_loop_contract(Some(&left), Some(&right)));
        });
    }

    #[test]
    fn loop_contract_equality_detects_citation_only_mutation() {
        create_default_session_globals_then(|| {
            let mut left = LoopContract::default();
            left.clauses.push(LoopClause {
                kind: LoopClauseKind::Invariant,
                keyword_span: DUMMY_SP,
                clause: native_clause("i < n", DUMMY_SP, None),
            });
            let mut right = left.clone();
            right.clauses[0].clause.citation = Some(citation(
                "Lemma.loop_bound",
                Span::with_root_ctxt(BytePos(1), BytePos(2)),
            ));

            assert!(!eq_loop_contract(Some(&left), Some(&right)));
        });
    }

    #[test]
    fn pprust_rewrite_guard_finds_a_nested_span_only_contract() {
        create_default_session_globals_then(|| {
            let mut contract = LoopContract::default();
            contract.clauses.push(LoopClause {
                kind: LoopClauseKind::Invariant,
                keyword_span: DUMMY_SP,
                clause: native_clause(
                    "i < n",
                    DUMMY_SP,
                    Some(citation("Lemma.nested", Span::with_root_ctxt(BytePos(1), BytePos(2)))),
                ),
            });
            let mut contract_loop = Expr::dummy();
            contract_loop.kind = ExprKind::While(
                Box::new(Expr::dummy()),
                Box::new(Block {
                    stmts: Default::default(),
                    id: DUMMY_NODE_ID,
                    rules: BlockCheckMode::Default,
                    span: DUMMY_SP,
                    tokens: None,
                }),
                None,
                Some(Box::new(contract)),
            );
            let pat = Pat {
                id: DUMMY_NODE_ID,
                kind: PatKind::Expr(Box::new(contract_loop)),
                span: DUMMY_SP,
                tokens: None,
            };

            assert!(pat_contains_authored_contract(&pat));
            assert!(!pat_contains_authored_contract(&Pat {
                kind: PatKind::Expr(Box::new(Expr::dummy())),
                ..pat
            }));
        });
    }

    #[test]
    fn pprust_rewrite_guard_handles_contracts_reached_through_visit_fn() {
        let mut finder = AuthoredVerifierSourceFinder::default();
        finder.visit_contract(&FnContract::default());
        assert!(finder.found);
    }

    #[test]
    fn parsed_attribute_equality_never_panics_or_guesses() {
        let cfg = AttrItemKind::Parsed(EarlyParsedAttribute::CfgTrace(CfgEntry::Bool(true, DUMMY_SP)));
        assert!(eq_attr_item_kind(&cfg, &cfg));

        let cfg_attr = AttrItemKind::Parsed(EarlyParsedAttribute::CfgAttrTrace);
        assert!(!eq_attr_item_kind(&cfg_attr, &cfg_attr));
    }

    #[test]
    fn pprust_rewrite_guard_classifies_clean_islands_as_authored_source() {
        assert!(item_kind_has_authored_verifier_source(&ItemKind::CleanIsland(DUMMY_SP)));
    }
}
