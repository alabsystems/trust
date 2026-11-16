// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Whether a declaration's OWN kernel value is already the body its plan
//! records — the wrapping op or tree of a `WrappingBinOp` / `Composed` plan,
//! the returned parameter of a `Projection`, the numeral of a `ConstantUint` —
//! read verbatim, with none of the planner's normalisations (named-call
//! expansion, metadata stripping) applied.
//!
//! The planner is allowed to see through a transparent Lean helper
//! (`named_calls`) or an elaborator annotation, because the carrier gate
//! compares against the ORIGINAL declaration by kernel defeq, which unfolds
//! both. The compiler's kernel-TV companion does not: it denotes the original
//! value syntactically (`clean_reflect::denote_source_in_environment`), with no
//! `MData` arm and without unfolding a Lean helper (the only names it resolves
//! in the checked source environment are named class dictionaries, read from
//! their stored fields), and a carrier-gated row whose companion is missing is a fatal
//! semantic-finalization error. So a shape may be *targeted* only when the
//! source is readable without those normalisations, and this module is the
//! test the gate's targeting decision asks.
//!
//! The grammar below is a deliberate SUBSET of `denote_source`'s fragment:
//! every form it accepts is one that function reads, with the same argument
//! counts and the same exact type checks. Anything else answers `false`,
//! which leaves the row untargeted at the tier it had before — never a new
//! refusal. Widening it without widening `denote_source` first would turn
//! that into a fatal, so it only ever moves after the denotation does.
//!
//! ```text
//! value ::= fun (x : UIntW) … (x : UIntW) => e      -- exactly `arity` binders
//! e     ::= bvar                                     -- a parameter or a let
//!         | UIntW.ofNat k | OfNat.ofNat UIntW k _    -- k a raw literal < 2^W
//!         | UIntW.{add,sub,mul} e e
//!         | H{Add,Sub,Mul}.h{add,sub,mul} UIntW UIntW UIntW _ e e
//!         | let _ : UIntW := e; e
//!         | cond _ c e e                             -- (α, cond, then, else)
//!         | Bool.rec _ e e c                         -- (motive, false, true, major)
//!         | Bool.casesOn _ c e e                     -- (motive, major, false, true)
//! c     ::= UIntW.{blt,ble,beq} e e
//! ```
//!
//! The three conditional forms and their condition are `denote_source`'s
//! Fragment-3a arm (`denote_source_cond`), transcribed with its argument
//! positions and its leniency: like it, the `cond` type and the recursor
//! motive are not inspected, and the comparison is recognized by its head's
//! NAME. None of them can be LIVE in a wrapping plan — the planner zetas every
//! `let` and admits only `+`/`-`/`*` nodes over parameters and numerals — so
//! here they only ever sit in a dead `let`, which the companion denotes
//! eagerly and then discards. Leaving them out made such a row untargeted
//! although the companion reads it and the gate admits it.
//!
//! No `MData` is accepted anywhere, at any position `denote_source` inspects.
//!
//! The two LEAF shapes ([`reads_leaf_directly`]) take the same telescope and
//! the same `let` grammar — every `let` value must read, because the
//! companion denotes it eagerly even when it is dead — and then require the
//! body, after the zeta substitution the companion itself performs, to be
//! EXACTLY the plan's leaf: parameter `projected`, or the in-range numeral
//! `value`, in the two numeral spellings above. That is stronger than
//! readability alone, and deliberately so: a readable body that is not that
//! leaf (`a + 0` under a `Projection` plan) would denote to a different term
//! than the emitted `Return`, so the companion would refuse and a targeted row
//! would again be fatal.

use clean_kernel::name::{Name, NameInner};
use clean_kernel::{Expr, ExprKind, Literal};

/// Deeper than any tree the planner admits (32 op nodes) plus its leaves and
/// lets; past it the answer is `false`, never a stack exhaustion.
const MAX_DEPTH: usize = 256;

fn width_uint(width: u32) -> Option<&'static str> {
    match width {
        8 => Some("UInt8"),
        16 => Some("UInt16"),
        32 => Some("UInt32"),
        64 => Some("UInt64"),
        _ => None,
    }
}

/// `true` iff `value` is, verbatim, `arity` `UIntW`-typed lambdas over a body
/// in the grammar of the module docs.
pub(crate) fn reads_directly(value: &Expr, arity: usize, width: u32) -> bool {
    let Some(uint) = width_uint(width) else {
        return false;
    };
    telescope_body(value, arity, uint)
        .is_some_and(|body| reads_value(body, &Ctx { uint, width, arity }, 0, 0))
}

/// The leaf a `Projection` or `ConstantUint` plan records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DirectLeaf {
    /// Source parameter `projected`, 0-based from the OUTERMOST binder — the
    /// planner's `CleanOriginShape::Projection { projected }` numbering.
    Param(usize),
    /// The in-range numeral of `CleanOriginShape::ConstantUint { value }`.
    Literal(u128),
}

/// `true` iff `value` is, verbatim, `arity` `UIntW`-typed lambdas over a body
/// that zeta-reduces to exactly `leaf`, every `let` on the way binding a
/// `UIntW` value in the [`reads_directly`] grammar (see the module docs).
pub(crate) fn reads_leaf_directly(
    value: &Expr,
    arity: usize,
    width: u32,
    leaf: DirectLeaf,
) -> bool {
    let Some(uint) = width_uint(width) else {
        return false;
    };
    telescope_body(value, arity, uint).is_some_and(|body| {
        leaf_value(body, &Ctx { uint, width, arity }, &mut Vec::new(), 0) == Some(leaf)
    })
}

/// Strip exactly `arity` lambdas, each binding `uint` and nothing else.
fn telescope_body<'e>(value: &'e Expr, arity: usize, uint: &str) -> Option<&'e Expr> {
    let mut body = value;
    let mut binders = 0usize;
    while let ExprKind::Lam(_, ty, inner) = body.kind() {
        if !is_const(ty, uint) {
            return None;
        }
        binders += 1;
        body = inner;
    }
    (binders == arity).then_some(body)
}

struct Ctx<'a> {
    uint: &'a str,
    width: u32,
    arity: usize,
}

#[inline]
fn split_app<'a, 'b, const N: usize>(
    mut e: &'a Expr,
    buf: &'b mut [&'a Expr; N],
) -> Option<(&'a Name, &'b [&'a Expr])> {
    let mut i = N;
    while let ExprKind::App(f, a) = e.kind() {
        i = i.checked_sub(1)?;
        buf[i] = a;
        e = f;
    }
    let ExprKind::Const(head, _) = e.kind() else {
        return None;
    };
    Some((head, &buf[i..]))
}

#[inline]
fn name_display_eq1(name: &Name, expected: &str) -> bool {
    matches!(name.inner(), NameInner::Str(parent, s) if parent.is_anon() && s.as_ref() == expected)
}

#[inline]
fn name_display_eq2(name: &Name, s0: &str, s1: &str) -> bool {
    match name.inner() {
        NameInner::Str(parent, last) if parent.is_anon() => {
            last.strip_prefix(s0).and_then(|rest| rest.strip_prefix('.')) == Some(s1)
        }
        NameInner::Str(parent, last) if last.as_ref() == s1 => name_display_eq1(parent, s0),
        _ => false,
    }
}

/// `lets` counts the enclosing source `let`s: a bvar below it names one, and
/// the next `arity` indices name the parameters.
fn reads_value(e: &Expr, cx: &Ctx<'_>, lets: usize, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    let next = depth + 1;
    match e.kind() {
        ExprKind::BVar(index) => {
            return usize::try_from(*index).is_ok_and(|index| index < lets + cx.arity);
        }
        ExprKind::Let(_, ty, value, body, _) => {
            return is_const(ty, cx.uint)
                && reads_value(value, cx, lets, next)
                && reads_value(body, cx, lets + 1, next);
        }
        _ => {}
    }
    let mut buf = [e; 6];
    let Some((head, args)) = split_app(e, &mut buf) else {
        return false;
    };
    let uint = cx.uint;
    match args {
        [literal] if name_display_eq2(head, uint, "ofNat") => in_range_literal(literal, cx.width),
        [ty, literal, _instance]
            if name_display_eq2(head, "OfNat", "ofNat") && is_const(ty, uint) =>
        {
            in_range_literal(literal, cx.width)
        }
        [left, right]
            if name_display_eq2(head, uint, "add")
                || name_display_eq2(head, uint, "sub")
                || name_display_eq2(head, uint, "mul") =>
        {
            reads_value(left, cx, lets, next) && reads_value(right, cx, lets, next)
        }
        [a, b, c, _instance, left, right]
            if (name_display_eq2(head, "HAdd", "hAdd")
                || name_display_eq2(head, "HSub", "hSub")
                || name_display_eq2(head, "HMul", "hMul"))
                && [a, b, c].iter().all(|ty| is_const(ty, uint)) =>
        {
            reads_value(left, cx, lets, next) && reads_value(right, cx, lets, next)
        }
        // `denote_source`'s Fragment-3a arm, in its argument order per head.
        [_ty, condition, then_arm, else_arm] if name_display_eq1(head, "cond") => {
            reads_condition(condition, cx, lets, next)
                && reads_value(then_arm, cx, lets, next)
                && reads_value(else_arm, cx, lets, next)
        }
        [_motive, false_arm, true_arm, major] if name_display_eq2(head, "Bool", "rec") => {
            reads_value(false_arm, cx, lets, next)
                && reads_value(true_arm, cx, lets, next)
                && reads_condition(major, cx, lets, next)
        }
        [_motive, major, false_arm, true_arm] if name_display_eq2(head, "Bool", "casesOn") => {
            reads_condition(major, cx, lets, next)
                && reads_value(false_arm, cx, lets, next)
                && reads_value(true_arm, cx, lets, next)
        }
        _ => false,
    }
}

/// What `e` is after the companion's zeta substitution, when that is a leaf:
/// a parameter (numbered as the planner numbers it) or an in-range numeral.
/// `lets` holds, innermost last, the leaf each enclosing source `let` binds —
/// `None` for a value that reads but is not a leaf (a dead `a + 1`), which a
/// body may then not return.
fn leaf_value(
    e: &Expr,
    cx: &Ctx<'_>,
    lets: &mut Vec<Option<DirectLeaf>>,
    depth: usize,
) -> Option<DirectLeaf> {
    if depth > MAX_DEPTH {
        return None;
    }
    match e.kind() {
        ExprKind::BVar(index) => {
            let index = usize::try_from(*index).ok()?;
            match index.checked_sub(lets.len()) {
                None => lets[lets.len() - 1 - index],
                Some(param) => (param < cx.arity).then(|| DirectLeaf::Param(cx.arity - 1 - param)),
            }
        }
        ExprKind::Let(_, ty, value, body, _) => {
            // The companion denotes every `let` value eagerly, live or dead.
            if !is_const(ty, cx.uint) || !reads_value(value, cx, lets.len(), depth + 1) {
                return None;
            }
            let bound = leaf_value(value, cx, lets, depth + 1);
            lets.push(bound);
            let result = leaf_value(body, cx, lets, depth + 1);
            lets.pop();
            result
        }
        _ => numeral_value(e, cx).map(|k| DirectLeaf::Literal(u128::from(k))),
    }
}

/// `UIntW.ofNat k` or `OfNat.ofNat UIntW k _` with `k` a raw literal < 2^W:
/// `k`. The same two arms, argument counts and range check as
/// [`reads_value`]'s (and `denote_source`'s) literal reading.
fn numeral_value(e: &Expr, cx: &Ctx<'_>) -> Option<u64> {
    let mut buf = [e; 3];
    let (head, args) = split_app(e, &mut buf)?;
    let uint = cx.uint;
    match args {
        [literal] if name_display_eq2(head, uint, "ofNat") => in_range_value(literal, cx.width),
        [ty, literal, _instance]
            if name_display_eq2(head, "OfNat", "ofNat") && is_const(ty, uint) =>
        {
            in_range_value(literal, cx.width)
        }
        _ => None,
    }
}

/// `denote_source_cond`: `UIntW.{blt,ble,beq} e e`, and nothing else.
fn reads_condition(e: &Expr, cx: &Ctx<'_>, lets: usize, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    let mut buf = [e; 2];
    let Some((head, args)) = split_app(e, &mut buf) else {
        return false;
    };
    let uint = cx.uint;
    match args {
        [left, right]
            if name_display_eq2(head, uint, "blt")
                || name_display_eq2(head, uint, "ble")
                || name_display_eq2(head, uint, "beq") =>
        {
            reads_value(left, cx, lets, depth + 1) && reads_value(right, cx, lets, depth + 1)
        }
        _ => false,
    }
}

fn is_const(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if name_display_eq1(n, name))
}

fn in_range_literal(e: &Expr, width: u32) -> bool {
    in_range_value(e, width).is_some()
}

fn in_range_value(e: &Expr, width: u32) -> Option<u64> {
    let ExprKind::Lit(Literal::Nat(value)) = e.kind() else {
        return None;
    };
    value.to_u64().filter(|&v| width == 64 || u128::from(v) < (1u128 << width))
}

#[cfg(test)]
mod tests {
    use clean_kernel::{BinderInfo, Expr, Name};

    use super::{DirectLeaf, reads_directly, reads_leaf_directly};

    fn c(name: &str) -> Expr {
        Expr::const_str(name)
    }

    fn lams(arity: usize, ty: &str, body: Expr) -> Expr {
        (0..arity).fold(body, |acc, _| Expr::lam(BinderInfo::Default, c(ty), acc))
    }

    /// `HAdd.hAdd UInt64 UInt64 UInt64 inst l r` and its siblings.
    fn surface(op: &str, ty: &str, left: Expr, right: Expr) -> Expr {
        let (class, method) = match op {
            "add" => ("HAdd", "hAdd"),
            "sub" => ("HSub", "hSub"),
            _ => ("HMul", "hMul"),
        };
        Expr::apps(c(&format!("{class}.{method}")), [c(ty), c(ty), c(ty), c("inst"), left, right])
    }

    fn carrier(op: &str, ty: &str, left: Expr, right: Expr) -> Expr {
        Expr::apps(c(&format!("{ty}.{op}")), [left, right])
    }

    fn numeral(ty: &str, k: u64) -> Expr {
        Expr::apps(c("OfNat.ofNat"), [c(ty), Expr::nat_lit(k), c("inst")])
    }

    /// `fun a b => (a + b) * a` with `a = bvar 1`, `b = bvar 0`.
    fn mix(ty: &str) -> Expr {
        lams(
            2,
            ty,
            surface("mul", ty, surface("add", ty, Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
        )
    }

    #[test]
    fn both_spellings_numerals_and_uint_lets_read_directly() {
        for w in [8, 16, 32, 64] {
            let ty = format!("UInt{w}");
            assert!(reads_directly(&mix(&ty), 2, w), "surface spelling at {ty}");
            let spelled = lams(
                2,
                &ty,
                carrier(
                    "mul",
                    &ty,
                    carrier("add", &ty, Expr::bvar(1), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            );
            assert!(reads_directly(&spelled, 2, w), "carrier spelling at {ty}");
            let max = u64::try_from((1_u128 << w) - 1).expect("fits");
            let literals = lams(
                1,
                &ty,
                surface(
                    "sub",
                    &ty,
                    numeral(&ty, max),
                    Expr::apps(c(&format!("{ty}.ofNat")), [Expr::nat_lit(3)]),
                ),
            );
            assert!(reads_directly(&literals, 1, w), "in-range literals at {ty}");
            // `let t : UIntW := a + 1; t * t` — bvar 0 is `t`, bvar 1 is `a`.
            let with_let = lams(
                1,
                &ty,
                Expr::let_named(
                    Name::from_string("t"),
                    c(&ty),
                    surface("add", &ty, Expr::bvar(0), numeral(&ty, 1)),
                    surface("mul", &ty, Expr::bvar(0), Expr::bvar(1)),
                    false,
                ),
            );
            assert!(reads_directly(&with_let, 1, w), "a UIntW let at {ty}");
        }
    }

    #[test]
    fn a_named_helper_head_is_not_direct_though_it_unfolds_to_the_same_tree() {
        // `nestedCall a := square (plusOne a)`: the planner expands it to
        // `(a + 1) * (a + 1)`; the source value itself is headed by `square`.
        let nested =
            lams(1, "UInt64", Expr::app(c("square"), Expr::app(c("plusOne"), Expr::bvar(0))));
        assert!(!reads_directly(&nested, 1, 64));
        // A helper at a leaf position is refused the same way.
        let leaf = lams(
            2,
            "UInt64",
            surface("add", "UInt64", Expr::app(c("plusOne"), Expr::bvar(1)), Expr::bvar(0)),
        );
        assert!(!reads_directly(&leaf, 2, 64));
    }

    #[test]
    fn metadata_anywhere_is_not_direct() {
        let tag = |e: Expr| Expr::mdata(Vec::new(), e);
        let inner = surface("add", "UInt64", Expr::bvar(1), Expr::bvar(0));
        for body in [
            tag(surface("mul", "UInt64", inner.clone(), Expr::bvar(1))),
            surface("mul", "UInt64", tag(inner.clone()), Expr::bvar(1)),
            surface("mul", "UInt64", inner.clone(), tag(Expr::bvar(1))),
        ] {
            assert!(!reads_directly(&lams(2, "UInt64", body), 2, 64));
        }
        let tagged_binder = Expr::lam(
            BinderInfo::Default,
            tag(c("UInt64")),
            lams(1, "UInt64", surface("mul", "UInt64", inner, Expr::bvar(1))),
        );
        assert!(!reads_directly(&tagged_binder, 2, 64));
    }

    #[test]
    fn every_other_boundary_answers_false() {
        // The unmodified control first, so each case below differs by one edit.
        assert!(reads_directly(&mix("UInt64"), 2, 64));
        // Arity disagrees with the signature.
        assert!(!reads_directly(&mix("UInt64"), 3, 64));
        // Width disagrees with the binder carrier, or is not a machine width.
        assert!(!reads_directly(&mix("UInt64"), 2, 32));
        assert!(!reads_directly(&mix("UInt7"), 2, 7));
        // A mixed-width telescope.
        let mixed = Expr::lam(
            BinderInfo::Default,
            c("UInt32"),
            Expr::lam(
                BinderInfo::Default,
                c("UInt64"),
                surface("mul", "UInt64", Expr::bvar(0), Expr::bvar(0)),
            ),
        );
        assert!(!reads_directly(&mixed, 2, 64));
        // A numeral out of range at the width (256 at UInt8) and a non-literal.
        let wide = lams(1, "UInt8", surface("add", "UInt8", Expr::bvar(0), numeral("UInt8", 256)));
        assert!(!reads_directly(&wide, 1, 8));
        let computed = lams(
            1,
            "UInt8",
            surface(
                "add",
                "UInt8",
                Expr::bvar(0),
                Expr::apps(c("OfNat.ofNat"), [c("UInt8"), Expr::bvar(0), c("inst")]),
            ),
        );
        assert!(!reads_directly(&computed, 1, 8));
        // A bvar escaping the telescope.
        let escape = lams(1, "UInt64", surface("add", "UInt64", Expr::bvar(0), Expr::bvar(1)));
        assert!(!reads_directly(&escape, 1, 64));
        // A let at another type.
        let nat_let = lams(
            1,
            "UInt64",
            Expr::let_named(
                Name::from_string("t"),
                c("Nat"),
                Expr::nat_lit(1),
                surface("add", "UInt64", Expr::bvar(1), Expr::bvar(1)),
                false,
            ),
        );
        assert!(!reads_directly(&nat_let, 1, 64));
        // A dispatcher at a heterogeneous type, and an op outside add/sub/mul.
        let hetero = lams(
            2,
            "UInt64",
            Expr::apps(
                c("HAdd.hAdd"),
                [c("UInt64"), c("UInt32"), c("UInt64"), c("inst"), Expr::bvar(1), Expr::bvar(0)],
            ),
        );
        assert!(!reads_directly(&hetero, 2, 64));
        let xor = lams(2, "UInt64", carrier("xor", "UInt64", Expr::bvar(1), Expr::bvar(0)));
        assert!(!reads_directly(&xor, 2, 64));
    }

    /// `let t : ty := v; (a + b)` with `a = bvar 2`, `b = bvar 1` under the
    /// let — the dead-let position, the only one a wrapping plan leaves a
    /// conditional in.
    fn dead_let(ty: &str, value: Expr) -> Expr {
        lams(
            2,
            ty,
            Expr::let_named(
                Name::from_string("t"),
                c(ty),
                value,
                surface("add", ty, Expr::bvar(2), Expr::bvar(1)),
                false,
            ),
        )
    }

    /// The three eliminator spellings `denote_source` reads, each with its
    /// own argument order, over `a` (bvar 1) and `b` (bvar 0).
    fn eliminators(ty: &str, condition: &Expr) -> [Expr; 3] {
        let motive = Expr::lam(BinderInfo::Default, c("Bool"), c(ty));
        [
            Expr::apps(c("cond"), [c(ty), condition.clone(), Expr::bvar(1), Expr::bvar(0)]),
            Expr::apps(
                c("Bool.rec"),
                [motive.clone(), Expr::bvar(0), Expr::bvar(1), condition.clone()],
            ),
            Expr::apps(
                c("Bool.casesOn"),
                [motive, condition.clone(), Expr::bvar(0), Expr::bvar(1)],
            ),
        ]
    }

    #[test]
    fn the_companions_conditional_family_reads_directly_in_every_spelling() {
        let mut read = 0;
        for w in [8, 16, 32, 64] {
            let ty = format!("UInt{w}");
            for comparison in ["blt", "ble", "beq"] {
                let condition =
                    Expr::apps(c(&format!("{ty}.{comparison}")), [Expr::bvar(1), Expr::bvar(0)]);
                for eliminator in eliminators(&ty, &condition) {
                    assert!(
                        reads_directly(&dead_let(&ty, eliminator.clone()), 2, w),
                        "{eliminator} in a dead let at {ty}"
                    );
                    read += 1;
                }
            }
            // Arms and comparison operands are values: literals and ops read.
            let condition = Expr::apps(
                c(&format!("{ty}.blt")),
                [surface("add", &ty, Expr::bvar(1), numeral(&ty, 1)), Expr::bvar(0)],
            );
            let [.., cases] = eliminators(&ty, &condition);
            assert!(reads_directly(&dead_let(&ty, cases), 2, w), "computed operands at {ty}");
        }
        assert_eq!(read, 36);
    }

    #[test]
    fn a_conditional_outside_the_companions_arm_answers_false() {
        let ty = "UInt64";
        let blt = |l: Expr, r: Expr| Expr::apps(c("UInt64.blt"), [l, r]);
        let control = blt(Expr::bvar(1), Expr::bvar(0));
        for eliminator in eliminators(ty, &control) {
            assert!(reads_directly(&dead_let(ty, eliminator), 2, 64), "the control reads");
        }
        let tag = |e: Expr| Expr::mdata(Vec::new(), e);
        for condition in [
            // `==` / `decide (a < b)` — what `match a == b` and `bif` elaborate to.
            Expr::apps(c("BEq.beq"), [c(ty), c("inst"), Expr::bvar(1), Expr::bvar(0)]),
            Expr::apps(c("Decidable.decide"), [c("prop"), c("inst")]),
            // Another width's comparison, a non-comparison head, a bare bvar.
            Expr::apps(c("UInt32.blt"), [Expr::bvar(1), Expr::bvar(0)]),
            Expr::apps(c("UInt64.bne"), [Expr::bvar(1), Expr::bvar(0)]),
            Expr::bvar(0),
            // Arity off by one either way.
            Expr::app(c("UInt64.blt"), Expr::bvar(1)),
            Expr::apps(c("UInt64.blt"), [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)]),
            // Metadata on the condition or on an operand, an unreadable operand.
            tag(control.clone()),
            blt(tag(Expr::bvar(1)), Expr::bvar(0)),
            blt(Expr::app(c("helper"), Expr::bvar(1)), Expr::bvar(0)),
        ] {
            for eliminator in eliminators(ty, &condition) {
                assert!(!reads_directly(&dead_let(ty, eliminator.clone()), 2, 64), "{eliminator}");
            }
        }
        // An unreadable arm, and each eliminator one argument short or long.
        let [cond_, rec_, cases] = eliminators(ty, &control);
        let helper_arm =
            Expr::apps(c("cond"), [c(ty), control.clone(), c("helper"), Expr::bvar(0)]);
        assert!(!reads_directly(&dead_let(ty, helper_arm), 2, 64));
        for eliminator in [cond_, rec_, cases] {
            let head = eliminator.get_app_fn().clone();
            let args: Vec<Expr> = eliminator.get_app_args().into_iter().cloned().collect();
            let short = Expr::apps(head.clone(), args[..3].to_vec());
            let long = Expr::apps(head, args.into_iter().chain([Expr::bvar(0)]));
            assert!(!reads_directly(&dead_let(ty, short), 2, 64));
            assert!(!reads_directly(&dead_let(ty, long), 2, 64));
        }
        // `Bool.rec`'s and `Bool.casesOn`'s major positions are not swappable.
        let motive = Expr::lam(BinderInfo::Default, c("Bool"), c(ty));
        let rec_major_first = Expr::apps(
            c("Bool.rec"),
            [motive.clone(), control.clone(), Expr::bvar(0), Expr::bvar(1)],
        );
        let cases_major_last =
            Expr::apps(c("Bool.casesOn"), [motive, Expr::bvar(0), Expr::bvar(1), control]);
        assert!(!reads_directly(&dead_let(ty, rec_major_first), 2, 64));
        assert!(!reads_directly(&dead_let(ty, cases_major_last), 2, 64));
    }

    fn let_(ty: &str, value: Expr, body: Expr) -> Expr {
        Expr::let_named(Name::from_string("t"), c(ty), value, body, false)
    }

    #[test]
    fn a_leaf_reads_directly_only_as_exactly_the_plans_leaf() {
        use DirectLeaf::{Literal, Param};
        for w in [8, 16, 32, 64] {
            let ty = format!("UInt{w}");
            let max = u64::try_from((1_u128 << w) - 1).expect("fits");
            let spelled = |k: u64| Expr::apps(c(&format!("{ty}.ofNat")), [Expr::nat_lit(k)]);
            // `fun a b => a` / `b`: parameter 0 is the OUTER binder (bvar 1).
            assert!(reads_leaf_directly(&lams(2, &ty, Expr::bvar(1)), 2, w, Param(0)));
            assert!(reads_leaf_directly(&lams(2, &ty, Expr::bvar(0)), 2, w, Param(1)));
            // Both numeral spellings, the max literal, and a nullary constant.
            assert!(reads_leaf_directly(
                &lams(1, &ty, numeral(&ty, max)),
                1,
                w,
                Literal(u128::from(max))
            ));
            assert!(reads_leaf_directly(&lams(2, &ty, spelled(7)), 2, w, Literal(7)));
            assert!(reads_leaf_directly(&numeral(&ty, 5), 0, w, Literal(5)));
            // A live `let` binding the leaf, and a readable dead `let`.
            let live = lams(2, &ty, let_(&ty, Expr::bvar(0), Expr::bvar(0)));
            assert!(reads_leaf_directly(&live, 2, w, Param(1)));
            let live_k = lams(1, &ty, let_(&ty, numeral(&ty, 9), Expr::bvar(0)));
            assert!(reads_leaf_directly(&live_k, 1, w, Literal(9)));
            let dead = lams(
                2,
                &ty,
                let_(&ty, surface("add", &ty, Expr::bvar(1), numeral(&ty, 1)), Expr::bvar(1)),
            );
            assert!(reads_leaf_directly(&dead, 2, w, Param(1)), "`let t := a + 1; b` at {ty}");
            // Mutation controls: each differs from a reading row by one edit.
            assert!(!reads_leaf_directly(&lams(2, &ty, Expr::bvar(1)), 2, w, Param(1)));
            assert!(!reads_leaf_directly(&lams(2, &ty, spelled(7)), 2, w, Literal(8)));
            assert!(!reads_leaf_directly(&lams(2, &ty, spelled(7)), 2, w, Param(0)));
            assert!(!reads_leaf_directly(&lams(2, &ty, Expr::bvar(0)), 2, w, Literal(0)));
            assert!(!reads_leaf_directly(&lams(2, &ty, Expr::bvar(0)), 1, w, Param(0)));
            assert!(!reads_leaf_directly(&lams(2, &ty, Expr::bvar(2)), 2, w, Param(0)));
            if w < 64 {
                let over = max + 1;
                assert!(!reads_leaf_directly(
                    &lams(1, &ty, numeral(&ty, over)),
                    1,
                    w,
                    Literal(u128::from(over))
                ));
            }
            // The let binds a non-leaf and the body returns it (`a + 1`).
            let returns_sum = lams(
                1,
                &ty,
                let_(&ty, surface("add", &ty, Expr::bvar(0), numeral(&ty, 1)), Expr::bvar(0)),
            );
            assert!(!reads_leaf_directly(&returns_sum, 1, w, Param(0)));
            // A readable body that is not a leaf: `a + 0` under a Projection plan.
            let plus_zero = lams(1, &ty, surface("add", &ty, Expr::bvar(0), numeral(&ty, 0)));
            assert!(reads_directly(&plus_zero, 1, w), "readable as arithmetic");
            assert!(!reads_leaf_directly(&plus_zero, 1, w, Param(0)), "but not the leaf");
        }
    }

    #[test]
    fn a_leaf_behind_a_helper_metadata_or_another_width_is_not_direct() {
        use DirectLeaf::{Literal, Param};
        let ty = "UInt64";
        let tag = |e: Expr| Expr::mdata(Vec::new(), e);
        // `pathPick a b := pick a b`, `useK a := kFive a`, `id b`.
        let helper_pick = lams(2, ty, Expr::apps(c("pick"), [Expr::bvar(1), Expr::bvar(0)]));
        assert!(!reads_leaf_directly(&helper_pick, 2, 64, Param(0)));
        let helper_k = lams(1, ty, Expr::app(c("kFive"), Expr::bvar(0)));
        assert!(!reads_leaf_directly(&helper_k, 1, 64, Literal(5)));
        let via_id = lams(2, ty, Expr::apps(c("id"), [c(ty), Expr::bvar(0)]));
        assert!(!reads_leaf_directly(&via_id, 2, 64, Param(1)));
        // A dead `let` the companion cannot denote, though the body is the leaf.
        let dead_helper = lams(
            2,
            ty,
            let_(ty, Expr::apps(c("pick"), [Expr::bvar(1), Expr::bvar(0)]), Expr::bvar(1)),
        );
        assert!(!reads_leaf_directly(&dead_helper, 2, 64, Param(1)));
        // A dead `let` at another type.
        let dead_bool = lams(
            2,
            ty,
            Expr::let_named(Name::from_string("t"), c("Bool"), c("true"), Expr::bvar(1), false),
        );
        assert!(!reads_leaf_directly(&dead_bool, 2, 64, Param(1)));
        // Metadata on the leaf, on a literal, on a binder type.
        assert!(!reads_leaf_directly(&lams(2, ty, tag(Expr::bvar(0))), 2, 64, Param(1)));
        assert!(!reads_leaf_directly(&lams(1, ty, tag(numeral(ty, 4))), 1, 64, Literal(4)));
        let tagged_binder = Expr::lam(BinderInfo::Default, tag(c(ty)), Expr::bvar(0));
        assert!(!reads_leaf_directly(&tagged_binder, 1, 64, Param(0)));
        // A mixed-width telescope (the companion binds ONE width) and a
        // numeral spelled at another width.
        let mixed = Expr::lam(BinderInfo::Default, c("UInt8"), lams(1, ty, Expr::bvar(0)));
        assert!(!reads_leaf_directly(&mixed, 2, 64, Param(1)));
        assert!(!reads_leaf_directly(&lams(1, ty, numeral("UInt32", 4)), 1, 64, Literal(4)));
        // A Nat-literal expression rather than a raw literal under `ofNat`.
        let nat_numeral = Expr::apps(c("OfNat.ofNat"), [c("Nat"), Expr::nat_lit(4), c("inst")]);
        let spelled = Expr::app(c("UInt64.ofNat"), nat_numeral);
        assert!(!reads_leaf_directly(&lams(1, ty, spelled), 1, 64, Literal(4)));
        // A width the companion has no carrier for.
        assert!(!reads_leaf_directly(&lams(1, "UInt128", Expr::bvar(0)), 1, 128, Param(0)));
    }

    #[test]
    fn an_adversarially_deep_value_answers_false_rather_than_recursing() {
        let mut body = Expr::bvar(0);
        for _ in 0..super::MAX_DEPTH + 8 {
            body = surface("add", "UInt64", body, Expr::bvar(0));
        }
        assert!(!reads_directly(&lams(1, "UInt64", body), 1, 64));
        let mut leaf = Expr::bvar(0);
        for _ in 0..super::MAX_DEPTH + 8 {
            leaf = let_("UInt64", Expr::bvar(0), leaf);
        }
        assert!(!reads_leaf_directly(&lams(1, "UInt64", leaf), 1, 64, DirectLeaf::Param(0)));
    }
}
