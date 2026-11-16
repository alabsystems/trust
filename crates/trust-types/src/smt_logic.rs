// trust-types/smt_logic.rs: Canonical SMT-LIB2 logic selection, free variable
// collection, and sort inference for Formula.
//
// Consolidated from trust_vcgen/smtlib2.rs, trust_vcgen/simplify_equivalence.rs,
// and trust-proof-cert/smt_equivalence.rs. This is the single authoritative location
// for these formula-level SMT utilities.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::borrow::Cow;
use std::collections::BTreeSet;

use crate::{Formula, Sort};

/// A recursively detected formula sort error.
///
/// `infer_sort` historically inspected only the outer constructor, so terms
/// such as `!(1)`, `true + 1`, and `true == 0` were all reported as well-sorted
/// predicates.  Source contracts and proof-cache keys must never accept that
/// shallow answer.  This error is intentionally structural and deterministic so
/// every caller can fail closed with a useful diagnostic.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum FormulaSortError {
    /// An operand had a different sort from the operator's required sort.
    #[error("{operator} requires {expected:?}, found {actual:?}")]
    Expected { operator: &'static str, expected: Sort, actual: Sort },
    /// Two operands that must have identical sorts disagreed.
    #[error("{operator} operands have different sorts: {left:?} and {right:?}")]
    Mismatch { operator: &'static str, left: Sort, right: Sort },
    /// A width-indexed operation disagreed with the sort carried by an operand.
    #[error("{operator} declares bit-width {declared}, but operand has width {actual}")]
    BitWidth { operator: &'static str, declared: u32, actual: u32 },
    /// A bitvector extraction range was empty or exceeded the input width.
    #[error("invalid bitvector extract [{high}:{low}] from width {width}")]
    InvalidExtract { high: u32, low: u32, width: u32 },
    /// A future formula variant is not yet checked and therefore cannot be trusted.
    #[error("formula variant has no recursive sort-checking rule")]
    UnsupportedVariant,
}

/// True iff `a` and `b` denote the SAME SMT sort.
///
/// Structural `Sort` equality is too strict for datatypes: trust-ir-contract
/// spells a datatype-typed FIELD, a pattern binder (`__fld_*`), an opaque
/// aggregate argument (`__dtf_*`) and `Sel::field_sort` as the BY-NAME
/// reference `Datatype { name, constructors: [] }` ("the datatype named
/// `name`, defined elsewhere"), while the definitional occurrence carries the
/// full constructor list. Both name one SMT-LIB sort — `(declare-datatype
/// Level …)` declares `Level` once and every term position refers to it by
/// name — so a datatype sort agrees with any other datatype sort of the same
/// name, recursively inside array sorts. Every other sort agrees only with
/// its structural equal.
///
/// SOUNDNESS: agreement by name cannot conflate two DIFFERENT datatypes — the
/// bridge (`DatatypeDefs::collect`) refuses two different full definitions
/// under one name before anything is lowered, and a by-name reference with no
/// definition in scope is refused at lowering. Agreement here only stops the
/// checker from calling an equation between a by-name and a full spelling of
/// one datatype a "mismatch" (which silently declined every
/// selector-vs-variable equation a recursive-datatype lane emits).
#[must_use]
pub fn sorts_agree(a: &Sort, b: &Sort) -> bool {
    match (a, b) {
        (Sort::Datatype { name: left, .. }, Sort::Datatype { name: right, .. }) => left == right,
        (Sort::Array(ai, ae), Sort::Array(bi, be)) => sorts_agree(ai, bi) && sorts_agree(ae, be),
        _ => a == b,
    }
}

/// Of two AGREEING sorts, the one that carries a datatype's full definition
/// (the by-name spelling contributes nothing a consumer could declare),
/// position by position inside array sorts.
fn definitional_sort(left: Sort, right: Sort) -> Sort {
    match (left, right) {
        (Sort::Datatype { constructors, .. }, right @ Sort::Datatype { .. })
            if constructors.is_empty() =>
        {
            right
        }
        (Sort::Array(li, le), Sort::Array(ri, re)) => Sort::Array(
            Box::new(definitional_sort(*li, *ri)),
            Box::new(definitional_sort(*le, *re)),
        ),
        (left, _) => left,
    }
}

fn needs_right_definitional(left: &Sort, right: &Sort) -> bool {
    match (left, right) {
        (Sort::Datatype { constructors, .. }, Sort::Datatype { constructors: r_ctors, .. }) => {
            constructors.is_empty() && !r_ctors.is_empty()
        }
        (Sort::Array(li, le), Sort::Array(ri, re)) => {
            needs_right_definitional(li, ri) || needs_right_definitional(le, re)
        }
        _ => false,
    }
}

fn definitional_sort_cow<'a>(left: Cow<'a, Sort>, right: Cow<'a, Sort>) -> Cow<'a, Sort> {
    if !needs_right_definitional(&left, &right) {
        return left;
    }
    if !needs_right_definitional(&right, &left) {
        return right;
    }
    Cow::Owned(definitional_sort(left.into_owned(), right.into_owned()))
}

const fn static_bitvec_sort(width: u32) -> Cow<'static, Sort> {
    match width {
        1 => Cow::Borrowed(&Sort::BitVec(1)),
        8 => Cow::Borrowed(&Sort::BitVec(8)),
        16 => Cow::Borrowed(&Sort::BitVec(16)),
        32 => Cow::Borrowed(&Sort::BitVec(32)),
        64 => Cow::Borrowed(&Sort::BitVec(64)),
        128 => Cow::Borrowed(&Sort::BitVec(128)),
        _ => Cow::Owned(Sort::BitVec(width)),
    }
}

const fn static_float_sort(eb: u32, sb: u32) -> Cow<'static, Sort> {
    match (eb, sb) {
        (5, 11) => Cow::Borrowed(&Sort::Float { eb: 5, sb: 11 }),
        (8, 24) => Cow::Borrowed(&Sort::Float { eb: 8, sb: 24 }),
        (11, 53) => Cow::Borrowed(&Sort::Float { eb: 11, sb: 53 }),
        (15, 113) => Cow::Borrowed(&Sort::Float { eb: 15, sb: 113 }),
        _ => Cow::Owned(Sort::Float { eb, sb }),
    }
}

fn expect_sort(
    operator: &'static str,
    actual: Cow<'_, Sort>,
    expected: Sort,
) -> Result<(), FormulaSortError> {
    if sorts_agree(&actual, &expected) {
        Ok(())
    } else {
        Err(FormulaSortError::Expected { operator, expected, actual: actual.into_owned() })
    }
}

fn expect_sort_ref(
    operator: &'static str,
    actual: Cow<'_, Sort>,
    expected: &Sort,
) -> Result<(), FormulaSortError> {
    if sorts_agree(&actual, expected) {
        Ok(())
    } else {
        Err(FormulaSortError::Expected {
            operator,
            expected: expected.clone(),
            actual: actual.into_owned(),
        })
    }
}

fn check_same_sort(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
) -> Result<(), FormulaSortError> {
    let left = check_formula_sort_cow(left)?;
    let right = check_formula_sort_cow(right)?;
    if sorts_agree(&left, &right) {
        Ok(())
    } else {
        Err(FormulaSortError::Mismatch {
            operator,
            left: left.into_owned(),
            right: right.into_owned(),
        })
    }
}

fn same_sort_cow<'a>(
    operator: &'static str,
    left: &'a Formula,
    right: &'a Formula,
) -> Result<Cow<'a, Sort>, FormulaSortError> {
    let left = check_formula_sort_cow(left)?;
    let right = check_formula_sort_cow(right)?;
    if sorts_agree(&left, &right) {
        Ok(definitional_sort_cow(left, right))
    } else {
        Err(FormulaSortError::Mismatch {
            operator,
            left: left.into_owned(),
            right: right.into_owned(),
        })
    }
}

fn int_binary(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
) -> Result<Cow<'static, Sort>, FormulaSortError> {
    expect_sort_ref(operator, check_formula_sort_cow(left)?, &Sort::Int)?;
    expect_sort_ref(operator, check_formula_sort_cow(right)?, &Sort::Int)?;
    Ok(Cow::Borrowed(&Sort::Int))
}

fn bv_operand(
    operator: &'static str,
    operand: &Formula,
    width: u32,
) -> Result<(), FormulaSortError> {
    let actual = check_formula_sort_cow(operand)?;
    match &*actual {
        Sort::BitVec(actual_width) if *actual_width == width => Ok(()),
        Sort::BitVec(actual_width) => {
            Err(FormulaSortError::BitWidth { operator, declared: width, actual: *actual_width })
        }
        _ => Err(FormulaSortError::Expected {
            operator,
            expected: Sort::BitVec(width),
            actual: actual.into_owned(),
        }),
    }
}

fn bv_binary(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
    width: u32,
) -> Result<Cow<'static, Sort>, FormulaSortError> {
    bv_operand(operator, left, width)?;
    bv_operand(operator, right, width)?;
    Ok(static_bitvec_sort(width))
}

fn float_operand(
    operator: &'static str,
    operand: &Formula,
    expected: &Sort,
) -> Result<(), FormulaSortError> {
    expect_sort_ref(operator, check_formula_sort_cow(operand)?, expected)
}

/// THE SORT-POSITION INVENTORY, for ONE node: every `Sort` that node carries
/// in its own fields.
///
/// This is the single list of sort positions in the workspace. Everything that
/// classifies, declares, gates or lowers a sort walks through it — the logic
/// line ([`select_logic`], trust-router's `detect_logic`), the declarations
/// (trust-router's `emit_declarations`), the datatype table
/// ([`crate::ay_bridge::DatatypeDefs::extend_from_formula`]) and the lowering
/// gates (trust-router's `visit_lowered_sort_positions`) — so they cannot
/// disagree about which sorts a formula mentions.
///
/// THE SIX POSITIONS, and why each is here:
///
/// 1. `Var(_, sort)` and 2. `SymVar(_, sort)` — the classic one; a free
///    variable is `declare-fun`'d at this sort.
/// 3. `Ctor { sort }` — a constructor application carries its own datatype
///    result sort. A GROUND constructor term reaches no `Var` at all.
/// 4. `Sel { field_sort }` — the selected field's sort; the term's sort.
/// 5. `FnApp { sort }` — an uninterpreted application's declared result sort.
///    `FnApp` only started lowering recently (it used to be a fail-closed
///    panic), which is why it is the position most recently missing from a
///    classifier.
/// 6. `Forall`/`Exists` BINDER sorts — THE BINDER-SORT HOLE.
///    `Formula::children()` returns `vec![body]` for the quantifiers, so a
///    binder's sorts are invisible to every `children()`-based recursion
///    (`visit`, `check_formula_sort`, the router's mismatch gates). A sort
///    that appears only in a binder therefore reaches the solver through
///    gates that never looked at it, and heads a transcript whose
///    `(set-logic ..)` never admitted it.
///
/// NOT a sort position, deliberately: `Sel { datatype }` and
/// `IsCtor { datatype }` name their datatype BY NAME (a `&str`, not a `Sort`);
/// see [`node_named_datatype_reference`], which callers combine with this one.
///
/// The caller supplies the traversal (`Formula::visit`) so a caller that must
/// short-circuit, or that needs the node as well as the sort, can. See
/// [`visit_sort_positions`] for the whole-formula convenience.
pub fn visit_node_sort_positions(node: &Formula, f: &mut impl FnMut(&Sort)) {
    match node {
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => f(sort),
        Formula::Ctor { sort, .. } | Formula::FnApp { sort, .. } => f(sort),
        Formula::Sel { field_sort, .. } => f(field_sort),
        // The binder sorts: NOT `children()`, and lowered/declared like any other.
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
            for (_, sort) in bindings {
                f(sort);
            }
        }
        // A constant array writes its whole sort into the term
        // (`((as const (Array I E)) v)`), so `(Array I E)` is a sort position
        // exactly like a `Var`'s: it must be declared, admitted by the logic
        // and lowerable. It is handed over as the one array sort it spells.
        Formula::ConstArray { index_sort, elem_sort, .. } => {
            f(&Sort::Array(Box::new(index_sort.clone()), Box::new(elem_sort.clone())));
        }
        _ => {}
    }
}

/// Every sort position anywhere in `formula`, in a deterministic pre-order
/// walk. The whole-formula form of [`visit_node_sort_positions`].
pub fn visit_sort_positions(formula: &Formula, f: &mut impl FnMut(&Sort)) {
    crate::visit_formula_nodes(formula, &mut |node| visit_node_sort_positions(node, f));
}

/// The datatype this node names BY NAME without carrying a `Sort` for it.
///
/// `Sel { datatype, .. }` and `IsCtor { datatype, .. }` range over a datatype
/// identified by a bare name: the sort identifier appears in the emitted term
/// (`(is-Const e)`, `(Expr_c e)`) and so must be in scope in the transcript and
/// admitted by its logic, but there is no `Sort` field to hand
/// [`visit_node_sort_positions`]. Callers that care about datatype PRESENCE
/// (logic selection) or about DECLARING the identifier (the SMT preamble) walk
/// this alongside the sort positions.
#[must_use]
pub fn node_named_datatype_reference(node: &Formula) -> Option<&str> {
    match node {
        Formula::Sel { datatype, .. } | Formula::IsCtor { datatype, .. } => Some(datatype.as_str()),
        _ => None,
    }
}

/// Recursively infer and validate the sort of every formula node.
///
/// Unlike [`infer_sort`], this exposes malformed children as a structured
/// error.  It is the required boundary for accepting source contracts,
/// reusable summaries, or other externally supplied formulas.
pub fn check_formula_sort(formula: &Formula) -> Result<Sort, FormulaSortError> {
    check_formula_sort_cow(formula).map(Cow::into_owned)
}

pub(crate) fn check_formula_sort_cow<'a>(
    formula: &'a Formula,
) -> Result<Cow<'a, Sort>, FormulaSortError> {
    match formula {
        Formula::Bool(_) => Ok(Cow::Borrowed(&Sort::Bool)),
        Formula::Int(_) | Formula::UInt(_) => Ok(Cow::Borrowed(&Sort::Int)),
        // An exact rational literal is a `Real` term — never an `Int` one, so an
        // Int-keyed consumer cannot mistake it for an integer constant.
        Formula::Rat { .. } => Ok(Cow::Borrowed(&Sort::Real)),
        Formula::BitVec { width, .. } => Ok(static_bitvec_sort(*width)),
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => Ok(Cow::Borrowed(sort)),

        Formula::Not(inner) => {
            expect_sort_ref("not", check_formula_sort_cow(inner)?, &Sort::Bool)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                expect_sort_ref("Boolean connective", check_formula_sort_cow(item)?, &Sort::Bool)?;
            }
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::Implies(left, right) => {
            expect_sort_ref("implication", check_formula_sort_cow(left)?, &Sort::Bool)?;
            expect_sort_ref("implication", check_formula_sort_cow(right)?, &Sort::Bool)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::Eq(left, right) => {
            check_same_sort("equality", left, right)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::Lt(left, right)
        | Formula::Le(left, right)
        | Formula::Gt(left, right)
        | Formula::Ge(left, right) => {
            // Int-Int is the classic fragment; a SAME-FORMAT float ordering
            // (`self.0 <= 1.0e30` — Float-sorted var vs binary64 literal, the
            // canonicalized magnitude-contract shape) is equally well-sorted:
            // the ay bridge lowers it to fp.lt/leq/gt/geq. Rejecting it here
            // silently turned EVERY float contract into the caller-side
            // `Bool(false)` fallback (an unprovable obligation at every call
            // site) — the def-contracts lane checks this exact function at
            // trust-mir-extract's parse boundary. Mixed or differing-format
            // operands still reject.
            let left_sort = check_formula_sort_cow(left)?;
            let right_sort = check_formula_sort_cow(right)?;
            match (&*left_sort, &*right_sort) {
                (Sort::Int, Sort::Int) => Ok(Cow::Borrowed(&Sort::Bool)),
                // Real-Real is the QF_LRA fragment (a ny-cert Farkas system over
                // real-valued network variables). Mixed Int/Real operands are
                // REJECTED, not coerced: an integer VARIABLE compared with a
                // real term would silently change which domain the atom
                // ranges over, and an integer literal in a Real position is
                // spelled `Formula::Rat` by its producer.
                (Sort::Real, Sort::Real) => Ok(Cow::Borrowed(&Sort::Bool)),
                (Sort::Float { eb: le, sb: ls }, Sort::Float { eb: re, sb: rs })
                    if le == re && ls == rs =>
                {
                    Ok(Cow::Borrowed(&Sort::Bool))
                }
                _ => {
                    expect_sort_ref("ordering comparison", left_sort, &Sort::Int)?;
                    expect_sort_ref("ordering comparison", right_sort, &Sort::Int)?;
                    Ok(Cow::Borrowed(&Sort::Bool))
                }
            }
        }

        // Linear arithmetic is sort-generic over the two arithmetic carriers:
        // Int-Int stays the classic fragment; Real-Real is the QF_LRA fragment.
        // Mixed operands reject (see the ordering arm above).
        Formula::Add(left, right) | Formula::Sub(left, right) | Formula::Mul(left, right) => {
            let left_sort = check_formula_sort_cow(left)?;
            let right_sort = check_formula_sort_cow(right)?;
            match (&*left_sort, &*right_sort) {
                (Sort::Real, Sort::Real) => Ok(Cow::Borrowed(&Sort::Real)),
                _ => {
                    expect_sort_ref("integer arithmetic", left_sort, &Sort::Int)?;
                    expect_sort_ref("integer arithmetic", right_sort, &Sort::Int)?;
                    Ok(Cow::Borrowed(&Sort::Int))
                }
            }
        }
        // `Div`/`Rem` are the Rust TRUNCATING integer operators (see the ay
        // bridge's lowering); they have no real-field meaning, so a `Real`
        // operand is ill-sorted here rather than silently lowered as integer
        // division.
        Formula::Div(left, right) | Formula::Rem(left, right) => {
            int_binary("integer arithmetic", left, right)
        }
        Formula::Neg(inner) => {
            let sort = check_formula_sort_cow(inner)?;
            if matches!(&*sort, Sort::Real) {
                Ok(Cow::Borrowed(&Sort::Real))
            } else {
                expect_sort_ref("integer negation", sort, &Sort::Int)?;
                Ok(Cow::Borrowed(&Sort::Int))
            }
        }

        Formula::BvAdd(left, right, width)
        | Formula::BvSub(left, right, width)
        | Formula::BvMul(left, right, width)
        | Formula::BvUDiv(left, right, width)
        | Formula::BvSDiv(left, right, width)
        | Formula::BvURem(left, right, width)
        | Formula::BvSRem(left, right, width)
        | Formula::BvAnd(left, right, width)
        | Formula::BvOr(left, right, width)
        | Formula::BvXor(left, right, width)
        | Formula::BvShl(left, right, width)
        | Formula::BvLShr(left, right, width)
        | Formula::BvAShr(left, right, width) => {
            bv_binary("bitvector binary operation", left, right, *width)
        }
        Formula::BvNot(inner, width) => {
            bv_operand("bitvector not", inner, *width)?;
            Ok(static_bitvec_sort(*width))
        }
        Formula::BvULt(left, right, width)
        | Formula::BvULe(left, right, width)
        | Formula::BvSLt(left, right, width)
        | Formula::BvSLe(left, right, width) => {
            bv_operand("bitvector comparison", left, *width)?;
            bv_operand("bitvector comparison", right, *width)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::BvToInt(inner, width, _) => {
            bv_operand("bitvector-to-int", inner, *width)?;
            Ok(Cow::Borrowed(&Sort::Int))
        }
        Formula::IntToBv(inner, width) => {
            expect_sort_ref("int-to-bitvector", check_formula_sort_cow(inner)?, &Sort::Int)?;
            Ok(static_bitvec_sort(*width))
        }
        Formula::BvExtract { inner, high, low } => {
            let actual = check_formula_sort_cow(inner)?;
            let Sort::BitVec(width) = *actual else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector extract",
                    expected: Sort::BitVec(high.saturating_add(1)),
                    actual: actual.into_owned(),
                });
            };
            if high < low || *high >= width {
                return Err(FormulaSortError::InvalidExtract { high: *high, low: *low, width });
            }
            Ok(static_bitvec_sort(high - low + 1))
        }
        Formula::BvConcat(left, right) => {
            let left_actual = check_formula_sort_cow(left)?;
            let Sort::BitVec(left_width) = *left_actual else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector concat",
                    expected: Sort::BitVec(1),
                    actual: left_actual.into_owned(),
                });
            };
            let right_actual = check_formula_sort_cow(right)?;
            let Sort::BitVec(right_width) = *right_actual else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector concat",
                    expected: Sort::BitVec(1),
                    actual: right_actual.into_owned(),
                });
            };
            Ok(static_bitvec_sort(left_width.saturating_add(right_width)))
        }
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => {
            let actual = check_formula_sort_cow(inner)?;
            if let Sort::BitVec(width) = *actual {
                Ok(static_bitvec_sort(width.saturating_add(*extra)))
            } else {
                Err(FormulaSortError::Expected {
                    operator: "bitvector extension",
                    expected: Sort::BitVec(1),
                    actual: actual.into_owned(),
                })
            }
        }

        Formula::FpConst { eb, sb, .. }
        | Formula::FpNaN { eb, sb }
        | Formula::FpInf { eb, sb, .. }
        | Formula::FpZero { eb, sb, .. } => Ok(static_float_sort(*eb, *sb)),
        Formula::FpRoundingMode(_) => Ok(Cow::Borrowed(&Sort::RoundingMode)),
        Formula::FpFromBits { bits, eb, sb } => {
            expect_sort_ref(
                "float-from-bits",
                check_formula_sort_cow(bits)?,
                &static_bitvec_sort(eb.saturating_add(*sb)),
            )?;
            Ok(static_float_sort(*eb, *sb))
        }
        Formula::FpToIeeeBv(inner) => {
            let actual = check_formula_sort_cow(inner)?;
            match *actual {
                Sort::Float { eb, sb } => Ok(static_bitvec_sort(eb.saturating_add(sb))),
                _ => Err(FormulaSortError::Expected {
                    operator: "float-to-bits",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: actual.into_owned(),
                }),
            }
        }
        Formula::FpAdd(round, left, right)
        | Formula::FpSub(round, left, right)
        | Formula::FpMul(round, left, right)
        | Formula::FpDiv(round, left, right) => {
            expect_sort_ref(
                "floating arithmetic",
                check_formula_sort_cow(round)?,
                &Sort::RoundingMode,
            )?;
            let sort = same_sort_cow("floating arithmetic", left, right)?;
            if matches!(&*sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating arithmetic",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                })
            }
        }
        Formula::FpFma(round, first, second, third) => {
            expect_sort_ref(
                "floating fused multiply-add",
                check_formula_sort_cow(round)?,
                &Sort::RoundingMode,
            )?;
            let sort = same_sort_cow("floating fused multiply-add", first, second)?;
            float_operand("floating fused multiply-add", third, &sort)?;
            if matches!(&*sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating fused multiply-add",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                })
            }
        }
        Formula::FpSqrt(round, inner) => {
            expect_sort_ref(
                "floating square root",
                check_formula_sort_cow(round)?,
                &Sort::RoundingMode,
            )?;
            let sort = check_formula_sort_cow(inner)?;
            if matches!(&*sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating square root",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                })
            }
        }
        // The five FP conversion nodes (2026-08-18). Added EXPLICITLY rather
        // than left to the wildcard below: the wildcard answers
        // `UnsupportedVariant`, which is fail-closed but would silently turn
        // every conversion-bearing effect ill-sorted — the exact
        // wildcard-absorbs-a-new-variant hazard this file's history warns
        // about.
        Formula::FpToSbv { rm, value, width, eb, sb }
        | Formula::FpToUbv { rm, value, width, eb, sb } => {
            expect_sort_ref(
                "floating to integer",
                check_formula_sort_cow(rm)?,
                &Sort::RoundingMode,
            )?;
            expect_sort_ref(
                "floating to integer",
                check_formula_sort_cow(value)?,
                &static_float_sort(*eb, *sb),
            )?;
            Ok(static_bitvec_sort(*width))
        }
        Formula::FpFromSbv { rm, value, eb, sb } | Formula::FpFromUbv { rm, value, eb, sb } => {
            expect_sort_ref(
                "integer to floating",
                check_formula_sort_cow(rm)?,
                &Sort::RoundingMode,
            )?;
            let sort = check_formula_sort_cow(value)?;
            if !matches!(&*sort, Sort::BitVec(_)) {
                return Err(FormulaSortError::Expected {
                    operator: "integer to floating",
                    expected: Sort::BitVec(64),
                    actual: sort.into_owned(),
                });
            }
            Ok(static_float_sort(*eb, *sb))
        }
        Formula::FpConvert { rm, value, eb, sb } => {
            expect_sort_ref(
                "floating format conversion",
                check_formula_sort_cow(rm)?,
                &Sort::RoundingMode,
            )?;
            let sort = check_formula_sort_cow(value)?;
            if !matches!(&*sort, Sort::Float { .. }) {
                return Err(FormulaSortError::Expected {
                    operator: "floating format conversion",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                });
            }
            Ok(static_float_sort(*eb, *sb))
        }
        Formula::FpRem(left, right) | Formula::FpMin(left, right) | Formula::FpMax(left, right) => {
            let sort = same_sort_cow("floating binary operation", left, right)?;
            if matches!(&*sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating binary operation",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                })
            }
        }
        Formula::FpNeg(inner) | Formula::FpAbs(inner) => {
            let sort = check_formula_sort_cow(inner)?;
            if matches!(&*sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating unary operation",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                })
            }
        }
        Formula::FpEq(left, right)
        | Formula::FpLt(left, right)
        | Formula::FpLe(left, right)
        | Formula::FpGt(left, right)
        | Formula::FpGe(left, right) => {
            let sort = same_sort_cow("floating comparison", left, right)?;
            if !matches!(&*sort, Sort::Float { .. }) {
                return Err(FormulaSortError::Expected {
                    operator: "floating comparison",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                });
            }
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::FpIsNaN(inner)
        | Formula::FpIsInfinite(inner)
        | Formula::FpIsZero(inner)
        | Formula::FpIsNormal(inner)
        | Formula::FpIsSubnormal(inner)
        | Formula::FpIsNegative(inner)
        | Formula::FpIsPositive(inner) => {
            let sort = check_formula_sort_cow(inner)?;
            if !matches!(&*sort, Sort::Float { .. }) {
                return Err(FormulaSortError::Expected {
                    operator: "floating classification",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort.into_owned(),
                });
            }
            Ok(Cow::Borrowed(&Sort::Bool))
        }

        Formula::Ite(condition, then_branch, else_branch) => {
            expect_sort_ref("if-then-else condition", check_formula_sort_cow(condition)?, &Sort::Bool)?;
            same_sort_cow("if-then-else", then_branch, else_branch)
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            expect_sort_ref("quantifier body", check_formula_sort_cow(body)?, &Sort::Bool)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::Select(array, index) => match check_formula_sort_cow(array)? {
            Cow::Borrowed(Sort::Array(index_sort, element_sort)) => {
                expect_sort_ref("array select", check_formula_sort_cow(index)?, index_sort)?;
                Ok(Cow::Borrowed(element_sort.as_ref()))
            }
            Cow::Owned(Sort::Array(index_sort, element_sort)) => {
                expect_sort("array select", check_formula_sort_cow(index)?, *index_sort)?;
                Ok(Cow::Owned(*element_sort))
            }
            actual => Err(FormulaSortError::Expected {
                operator: "array select",
                expected: Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                actual: actual.into_owned(),
            }),
        },
        Formula::Store(array, index, value) => match check_formula_sort_cow(array)? {
            Cow::Borrowed(arr_sort @ Sort::Array(index_sort, element_sort)) => {
                expect_sort_ref("array store index", check_formula_sort_cow(index)?, index_sort)?;
                expect_sort_ref("array store value", check_formula_sort_cow(value)?, element_sort)?;
                Ok(Cow::Borrowed(arr_sort))
            }
            Cow::Owned(Sort::Array(index_sort, element_sort)) => {
                expect_sort_ref("array store index", check_formula_sort_cow(index)?, &index_sort)?;
                expect_sort_ref("array store value", check_formula_sort_cow(value)?, &element_sort)?;
                Ok(Cow::Owned(Sort::Array(index_sort, element_sort)))
            }
            actual => Err(FormulaSortError::Expected {
                operator: "array store",
                expected: Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                actual: actual.into_owned(),
            }),
        },
        // `((as const (Array I E)) v)`: `v` must have the carried element sort.
        Formula::ConstArray { index_sort, elem_sort, value } => {
            expect_sort_ref("constant array value", check_formula_sort_cow(value)?, elem_sort)?;
            Ok(Cow::Owned(Sort::Array(Box::new(index_sort.clone()), Box::new(elem_sort.clone()))))
        }
        Formula::Pred(_, arguments) => {
            for argument in arguments {
                check_formula_sort_cow(argument)?;
            }
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        Formula::Ctor { args, sort, .. } | Formula::FnApp { args, sort, .. } => {
            for argument in args {
                check_formula_sort_cow(argument)?;
            }
            Ok(Cow::Borrowed(sort))
        }
        Formula::Sel { arg, field_sort, .. } => {
            check_formula_sort_cow(arg)?;
            Ok(Cow::Borrowed(field_sort))
        }
        Formula::IsCtor { arg, .. } => {
            check_formula_sort_cow(arg)?;
            Ok(Cow::Borrowed(&Sort::Bool))
        }
        #[allow(unreachable_patterns)]
        _ => Err(FormulaSortError::UnsupportedVariant),
    }
}

/// Select the appropriate SMT-LIB2 logic name for `formula`.
///
/// A TOTAL function of the formula's FEATURE SET, not a cascade of early
/// returns: [`crate::logic_lattice::formula_theories`] computes the whole
/// record first — every sort position, every by-name datatype reference and
/// every literal/operator — and [`crate::logic_lattice::select_logic_name`]
/// then makes ONE decision over all the bits, choosing a minimal logic name in
/// the shared admissibility table that admits every feature present.
///
/// WHY NOT A CASCADE. The previous implementation returned on a PREFIX of the
/// features: its floating-point arm fired before anything read `has_real`, so
/// a formula mixing an `fp.*` term with a `Real`-sorted variable was headed
/// `(set-logic QF_FP)` while its own `(declare-fun … Real)` line sat below it.
/// trust-router's `detect_logic` had the same defect one dimension over (FP
/// mixed with `Int`), which is what made both lanes read one table instead.
///
/// THE INVARIANT, proved by exhaustive enumeration of the entire 2^9 feature
/// powerset in `logic_lattice`'s tests: ADMISSIBILITY — the chosen name admits
/// every feature present. The ninth dimension is LINEARITY, so a formula with a
/// `Mul` of two non-literal operands heads `QF_NIA`, not `QF_LIA`; the UF
/// dimension is the sixth, so a formula applying a `Pred`/`FnApp` of arity >= 1
/// can never be answered a name that does not admit uninterpreted functions
/// (`logic_lattice`'s `no_public_selection_answers_a_logic_that_refuses_applied_uf`
/// pins that through THIS function). That is what this function, a SINGLE-FORMULA caller,
/// needs and all it needs. Monotonicity (a larger feature set never selecting a
/// name admitting less) is NOT a property of the table and is not claimed; the
/// group and batch callers that would have wanted it select once from the UNION
/// of their members' records instead, which admissibility alone covers. See
/// `logic_lattice`'s module header for the exact characterization of where
/// monotonicity fails, and [`crate::logic_lattice::select_logic_name`] for the
/// audit of every call site.
///
/// TRAVERSAL. The sort-derived bits come from the ONE shared inventory
/// ([`visit_node_sort_positions`] plus [`node_named_datatype_reference`]), the
/// same list the declaration emitters read; only the LITERAL/OPERATOR bits are
/// classified from the node itself, by
/// [`crate::logic_lattice::node_theories`]. A classifier with its own private
/// list of `Var` arms is how the `Ctor`/`Sel`/`FnApp`/binder sort positions kept
/// being left out of one walker while another declared them.
///
/// trust-router's transcript lane calls the SAME selector through
/// `smt2_export::detect_logic`, adding one further source on top of this one —
/// the `declare-fun` signature map it declares uninterpreted symbols from — so
/// the two lanes can differ only in which features they SEE, never in which
/// name a feature set maps to.
#[must_use]
pub fn select_logic(formula: &Formula) -> &'static str {
    crate::logic_lattice::select_logic_name(crate::logic_lattice::formula_theories(formula))
}

/// Collect all free variable declarations from a formula.
///
/// Returns a sorted `BTreeSet` of `(name, sort)` pairs for deterministic
/// output, excluding quantifier-bound names.
///
/// THE ONE FREE-VARIABLE COLLECTOR. Both string-backed [`Formula::Var`] and
/// interned [`Formula::SymVar`] nodes come through here, and so does
/// trust-router's `smt2_export::collect_free_vars`, which delegates to this
/// function — the native AY program, its canonical SMT transcript, the
/// external-solver script and the binary VC report therefore cannot disagree
/// about which variables a formula declares.
///
/// SCOPE IS TRACKED STRUCTURALLY, not by a name-membership test. The previous
/// implementation asked `formula.free_variables()` for the set of free NAMES
/// and then collected every `Var`/`SymVar` node whose name was in it, so a name
/// that is BOUND in one subterm and FREE in another contributed BOTH
/// occurrences: `And([Exists([(x, Int)], p(x)), Eq(Var(x, BitVec(8)), …)])`
/// yielded `("x", Int)` AND `("x", BitVec(8))` — two `(declare-fun x …)` lines
/// for one symbol, which is a malformed query. Walking the binder scope down
/// the tree, as below, cannot produce that.
#[must_use]
pub fn collect_free_var_decls(formula: &Formula) -> BTreeSet<(String, Sort)> {
    fn record<'a>(
        name: &'a str,
        sort: &'a Sort,
        bound_names: &[&str],
        seen: &mut crate::fx::FxHashSet<(&'a str, &'a Sort)>,
        free_vars: &mut BTreeSet<(String, Sort)>,
    ) {
        if !bound_names.contains(&name) && seen.insert((name, sort)) {
            free_vars.insert((name.to_string(), sort.clone()));
        }
    }

    fn collect<'a>(
        formula: &'a Formula,
        bound_names: &mut Vec<&'a str>,
        seen: &mut crate::fx::FxHashSet<(&'a str, &'a Sort)>,
        free_vars: &mut BTreeSet<(String, Sort)>,
    ) {
        match formula {
            Formula::Var(name, sort) => {
                record(name.as_str(), sort, bound_names, seen, free_vars);
            }
            Formula::SymVar(name, sort) => {
                record(name.as_str(), sort, bound_names, seen, free_vars);
            }
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let prev_len = bound_names.len();
                bound_names.extend(bindings.iter().map(|(name, _)| name.as_str()));
                collect(body, bound_names, seen, free_vars);
                bound_names.truncate(prev_len);
            }
            Formula::Not(a)
            | Formula::Neg(a)
            | Formula::BvNot(a, _)
            | Formula::BvToInt(a, _, _)
            | Formula::IntToBv(a, _)
            | Formula::BvExtract { inner: a, .. }
            | Formula::BvZeroExt(a, _)
            | Formula::BvSignExt(a, _)
            | Formula::FpFromBits { bits: a, .. }
            | Formula::FpToIeeeBv(a)
            | Formula::FpNeg(a)
            | Formula::FpAbs(a)
            | Formula::FpIsNaN(a)
            | Formula::FpIsInfinite(a)
            | Formula::FpIsZero(a)
            | Formula::FpIsNormal(a)
            | Formula::FpIsSubnormal(a)
            | Formula::FpIsNegative(a)
            | Formula::FpIsPositive(a)
            | Formula::ConstArray { value: a, .. }
            | Formula::Sel { arg: a, .. }
            | Formula::IsCtor { arg: a, .. } => {
                collect(a, bound_names, seen, free_vars);
            }
            Formula::Implies(a, b)
            | Formula::Eq(a, b)
            | Formula::Lt(a, b)
            | Formula::Le(a, b)
            | Formula::Gt(a, b)
            | Formula::Ge(a, b)
            | Formula::Add(a, b)
            | Formula::Sub(a, b)
            | Formula::Mul(a, b)
            | Formula::Div(a, b)
            | Formula::Rem(a, b)
            | Formula::BvAdd(a, b, _)
            | Formula::BvSub(a, b, _)
            | Formula::BvMul(a, b, _)
            | Formula::BvUDiv(a, b, _)
            | Formula::BvSDiv(a, b, _)
            | Formula::BvURem(a, b, _)
            | Formula::BvSRem(a, b, _)
            | Formula::BvAnd(a, b, _)
            | Formula::BvOr(a, b, _)
            | Formula::BvXor(a, b, _)
            | Formula::BvShl(a, b, _)
            | Formula::BvLShr(a, b, _)
            | Formula::BvAShr(a, b, _)
            | Formula::BvULt(a, b, _)
            | Formula::BvULe(a, b, _)
            | Formula::BvSLt(a, b, _)
            | Formula::BvSLe(a, b, _)
            | Formula::BvConcat(a, b)
            | Formula::FpSqrt(a, b)
            | Formula::FpToSbv { rm: a, value: b, .. }
            | Formula::FpToUbv { rm: a, value: b, .. }
            | Formula::FpFromSbv { rm: a, value: b, .. }
            | Formula::FpFromUbv { rm: a, value: b, .. }
            | Formula::FpConvert { rm: a, value: b, .. }
            | Formula::FpRem(a, b)
            | Formula::FpMin(a, b)
            | Formula::FpMax(a, b)
            | Formula::FpEq(a, b)
            | Formula::FpLt(a, b)
            | Formula::FpLe(a, b)
            | Formula::FpGt(a, b)
            | Formula::FpGe(a, b)
            | Formula::Select(a, b) => {
                collect(a, bound_names, seen, free_vars);
                collect(b, bound_names, seen, free_vars);
            }
            Formula::FpAdd(a, b, c)
            | Formula::FpSub(a, b, c)
            | Formula::FpMul(a, b, c)
            | Formula::FpDiv(a, b, c)
            | Formula::Ite(a, b, c)
            | Formula::Store(a, b, c) => {
                collect(a, bound_names, seen, free_vars);
                collect(b, bound_names, seen, free_vars);
                collect(c, bound_names, seen, free_vars);
            }
            Formula::FpFma(a, b, c, d) => {
                collect(a, bound_names, seen, free_vars);
                collect(b, bound_names, seen, free_vars);
                collect(c, bound_names, seen, free_vars);
                collect(d, bound_names, seen, free_vars);
            }
            Formula::And(items)
            | Formula::Or(items)
            | Formula::Pred(_, items)
            | Formula::Ctor { args: items, .. }
            | Formula::FnApp { args: items, .. } => {
                for item in items {
                    collect(item, bound_names, seen, free_vars);
                }
            }
            Formula::Bool(_)
            | Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Rat { .. }
            | Formula::BitVec { .. }
            | Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_) => {}
            _ => {
                crate::for_each_formula_child(formula, |child| {
                    collect(child, bound_names, seen, free_vars);
                });
            }
        }
    }

    let mut free_vars = BTreeSet::new();
    let mut bound_names = Vec::new();
    let mut seen = crate::fx::FxHashSet::default();
    collect(formula, &mut bound_names, &mut seen, &mut free_vars);
    free_vars
}

/// Infer the SMT-LIB2 sort for a formula expression.
///
/// Returns the sort that the top-level expression evaluates to:
/// - Boolean connectives (And, Or, Not, Implies) and comparisons -> `Sort::Bool`
/// - Integer arithmetic (Add, Sub, Mul, Div, Rem, Neg) -> `Sort::Int`
/// - Integer/UInt/Bool literals -> their natural sort
/// - Bitvector operations -> `Sort::BitVec(width)`
/// - Variables -> their declared sort
/// - Quantifiers -> `Sort::Bool`
/// - Select -> element sort (if array sort known), else `Sort::Int`
/// - Store -> array sort (if known), else `Sort::Int`
/// - Ite -> sort of the then-branch
/// - Datatype terms -> the result sort the node CARRIES: a constructor
///   application (`Ctor`) its datatype sort, a selector application (`Sel`)
///   its `field_sort`, a constructor tester (`IsCtor`) `Bool`; an
///   uninterpreted application (`FnApp`) its carried result sort and an
///   uninterpreted predicate (`Pred`) `Bool`
///
/// Defaults to `Sort::Int` for ambiguous cases. Every variant of the
/// trust-ir-contract `Formula` has an arm below, so the wildcard is reached
/// only for a FUTURE `#[non_exhaustive]` variant — and such a variant already
/// fails [`check_formula_sort`] (`UnsupportedVariant`), which the guard at the
/// top turns into the same non-predicate `Int` sentinel. A caller that must
/// not act on that sentinel (a pre-check that DECLINES on a sort mismatch)
/// uses [`check_formula_sort`] on the operands instead: `Int` from this
/// function is an answer, never a proof of ignorance.
#[must_use]
pub fn infer_sort(formula: &Formula) -> Sort {
    infer_sort_cow(formula).into_owned()
}

#[must_use]
pub(crate) fn infer_sort_cow(formula: &Formula) -> Cow<'_, Sort> {
    // Keep the long-standing total return type for broad solver plumbing, but
    // never report an ill-typed predicate as Boolean.  Callers that need the
    // diagnostic use `check_formula_sort`; legacy callers receive the
    // conservative non-predicate sentinel `Int` on any recursive error.
    if check_formula_sort_cow(formula).is_err() {
        return Cow::Borrowed(&Sort::Int);
    }
    infer_sort_checked_cow(formula)
}

fn infer_sort_checked_cow<'a>(formula: &'a Formula) -> Cow<'a, Sort> {
    match formula {
        // Literals
        Formula::Bool(_) => Cow::Borrowed(&Sort::Bool),
        Formula::Int(_) | Formula::UInt(_) => Cow::Borrowed(&Sort::Int),
        Formula::Rat { .. } => Cow::Borrowed(&Sort::Real),
        Formula::BitVec { width, .. } => static_bitvec_sort(*width),

        // Variables carry their own sort
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => Cow::Borrowed(sort),

        // Boolean connectives and comparisons
        Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(_, _)
        | Formula::Eq(_, _)
        | Formula::Lt(_, _)
        | Formula::Le(_, _)
        | Formula::Gt(_, _)
        | Formula::Ge(_, _)
        | Formula::BvULt(_, _, _)
        | Formula::BvULe(_, _, _)
        | Formula::BvSLt(_, _, _)
        | Formula::BvSLe(_, _, _) => Cow::Borrowed(&Sort::Bool),

        // Linear arithmetic is sort-generic (Int or Real carrier); the guard
        // above already established both operands agree, so the left operand
        // decides. `Div`/`Rem` are Int-only.
        Formula::Add(a, _) | Formula::Sub(a, _) | Formula::Mul(a, _) | Formula::Neg(a) => {
            match &*infer_sort_checked_cow(a) {
                Sort::Real => Cow::Borrowed(&Sort::Real),
                _ => Cow::Borrowed(&Sort::Int),
            }
        }
        Formula::Div(_, _) | Formula::Rem(_, _) => Cow::Borrowed(&Sort::Int),

        // Bitvector arithmetic -- width from the operation
        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvSDiv(_, _, w)
        | Formula::BvURem(_, _, w)
        | Formula::BvSRem(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvNot(_, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w) => static_bitvec_sort(*w),

        // Bitvector conversions
        Formula::BvToInt(_, _, _) => Cow::Borrowed(&Sort::Int),
        Formula::IntToBv(_, w) => static_bitvec_sort(*w),
        Formula::BvExtract { high, low, .. } => static_bitvec_sort(high - low + 1),
        Formula::BvConcat(a, b) => {
            let wa = match *infer_sort_checked_cow(a) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            let wb = match *infer_sort_checked_cow(b) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            static_bitvec_sort(wa + wb)
        }
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => {
            let base = match *infer_sort_checked_cow(inner) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            static_bitvec_sort(base + extra)
        }

        // FloatingPoint — literals/typed nodes carry their format directly.
        Formula::FpConst { eb, sb, .. }
        | Formula::FpNaN { eb, sb }
        | Formula::FpInf { eb, sb, .. }
        | Formula::FpZero { eb, sb, .. }
        | Formula::FpFromBits { eb, sb, .. } => static_float_sort(*eb, *sb),
        Formula::FpRoundingMode(_) => Cow::Borrowed(&Sort::RoundingMode),
        // `(fp.to_ieee_bv <fp>)` yields an `(eb+sb)`-wide bitvector; recover the
        // format from the FP operand's sort. (The inverse of `FpFromBits`, whose
        // result is the Float sort.)
        Formula::FpToIeeeBv(a) => match *infer_sort_checked_cow(a) {
            Sort::Float { eb, sb } => static_bitvec_sort(eb + sb),
            _ => static_bitvec_sort(64),
        },
        // FP arithmetic — recover the format from a float operand.
        Formula::FpAdd(_, a, _)
        | Formula::FpSub(_, a, _)
        | Formula::FpMul(_, a, _)
        | Formula::FpDiv(_, a, _)
        | Formula::FpFma(_, a, _, _)
        | Formula::FpSqrt(_, a)
        | Formula::FpRem(a, _)
        | Formula::FpMin(a, _)
        | Formula::FpMax(a, _)
        | Formula::FpNeg(a)
        | Formula::FpAbs(a) => infer_sort_checked_cow(a),
        // FP comparisons and classification predicates are Bool.
        Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpIsNaN(..)
        | Formula::FpIsInfinite(..)
        | Formula::FpIsZero(..)
        | Formula::FpIsNormal(..)
        | Formula::FpIsSubnormal(..)
        | Formula::FpIsNegative(..)
        | Formula::FpIsPositive(..) => Cow::Borrowed(&Sort::Bool),

        // Conditional -- sort of the then-branch
        Formula::Ite(_, then_br, _) => infer_sort_checked_cow(then_br),

        // Quantifiers always produce Bool
        Formula::Forall(_, _) | Formula::Exists(_, _) => Cow::Borrowed(&Sort::Bool),

        // Array operations
        Formula::Select(arr, _) => match infer_sort_checked_cow(arr) {
            Cow::Borrowed(Sort::Array(_, elem)) => Cow::Borrowed(elem.as_ref()),
            Cow::Owned(Sort::Array(_, elem)) => Cow::Owned(*elem),
            _ => Cow::Borrowed(&Sort::Int),
        },
        Formula::Store(arr, _, _) => infer_sort_checked_cow(arr),
        Formula::ConstArray { index_sort, elem_sort, .. } => {
            Cow::Owned(Sort::Array(Box::new(index_sort.clone()), Box::new(elem_sort.clone())))
        }

        // Datatype terms and uninterpreted applications carry their result
        // sort on the node (trust-ir-contract `Formula`): a `Ctor` its own
        // `Sort::Datatype`, a `Sel` the selected field's sort, an `FnApp` its
        // declared result sort. Testers and predicates are Bool by definition.
        // Before these arms every such term fell to the `Int` wildcard, so a
        // well-sorted `succ(l) = l` read as `Int` vs `Level` — a "mismatch"
        // `check_formula_sort` (which already had these rules) never reported.
        Formula::Ctor { sort, .. } | Formula::FnApp { sort, .. } => Cow::Borrowed(sort),
        Formula::Sel { field_sort, .. } => Cow::Borrowed(field_sort),
        Formula::IsCtor { .. } | Formula::Pred(..) => Cow::Borrowed(&Sort::Bool),

        // Conservative fallback for future #[non_exhaustive] variants (already
        // refused by the `check_formula_sort` guard above, so this is the same
        // non-predicate sentinel that guard returns — see the function docs).
        #[allow(unreachable_patterns)]
        _ => Cow::Borrowed(&Sort::Int),
    }
}

/// Split an s-expression body into its top-level tokens/sub-expressions.
///
/// Canonical s-expression splitter shared by `SmtPrinter` and
/// `SmtLib2Printer`. Handles nested parentheses, whitespace tokenization,
/// and trailing tokens.
///
/// # Example
/// ```text
/// split_top_level("and (> x 0) (< y 10)")
/// // => ["and", "(> x 0)", "(< y 10)"]
/// ```
#[must_use]
pub fn split_top_level(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start: Option<usize> = None;
    for (i, &b) in input.as_bytes().iter().enumerate() {
        match b {
            b' ' | b'\t' | b'\n' if depth == 0 => {
                if let Some(s) = start {
                    let token = &input[s..i];
                    if !token.trim().is_empty() {
                        parts.push(token);
                    }
                    start = None;
                }
            }
            b'(' => {
                if start.is_none() {
                    start = Some(i);
                }
                depth += 1;
            }
            b')' => {
                depth = depth.saturating_sub(1);
                if depth == 0
                    && let Some(s) = start
                {
                    parts.push(&input[s..=i]);
                    start = None;
                }
            }
            _ => {
                if start.is_none() {
                    start = Some(i);
                }
            }
        }
    }
    // Trailing token.
    if let Some(s) = start {
        let token = &input[s..];
        if !token.trim().is_empty() {
            parts.push(token);
        }
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Sort};

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    #[test]
    fn recursive_sort_checker_rejects_malformed_children() {
        let bool_var = Formula::Var("flag".into(), Sort::Bool);
        let int_var = Formula::Var("n".into(), Sort::Int);
        let malformed = [
            Formula::Gt(
                Box::new(Formula::Add(Box::new(bool_var.clone()), Box::new(Formula::Int(1)))),
                Box::new(Formula::Int(0)),
            ),
            Formula::Not(Box::new(int_var.clone())),
            Formula::Eq(Box::new(bool_var), Box::new(int_var)),
        ];
        for formula in malformed {
            assert!(check_formula_sort(&formula).is_err(), "accepted {formula:?}");
            assert_ne!(infer_sort(&formula), Sort::Bool);
        }
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // --- select_logic ---

    #[test]
    fn test_select_logic_pure_int() {
        let f = Formula::Add(Box::new(var("x")), Box::new(Formula::Int(1)));
        assert_eq!(select_logic(&f), "QF_LIA");
    }

    #[test]
    fn test_select_logic_pure_bv() {
        let f = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        assert_eq!(select_logic(&f), "QF_BV");
    }

    #[test]
    fn test_select_logic_quantified() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(select_logic(&f), "LIA");
    }

    #[test]
    fn test_select_logic_array_int() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "arr".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            )),
            Box::new(var("i")),
        );
        assert_eq!(select_logic(&f), "QF_ALIA");
    }

    /// Arrays OF bitvectors take `QF_ABV` — the name that spells exactly what
    /// the query uses.
    ///
    /// A previous revision answered `ALL` here, because a FULLY MONOTONE table
    /// cannot hold `QF_ABV` and `QF_ALIA` at once: `{Arrays}` is a subset of
    /// both, so it would have to select a name admitting no more than
    /// `QF_ALIA ∩ QF_ABV = {Arrays}`, which no SMT-LIB name spells. Monotonicity
    /// is no longer claimed (`logic_lattice`'s
    /// `monotonicity_fails_only_from_sets_no_row_names_exactly` says exactly
    /// where it fails), so the precise name is back and a bitvector query
    /// reaches a bitvector pipeline. (`{Arrays}` alone IS spelled by SMT-LIB,
    /// `QF_AX`, and the name audit added that row; it is not this query's
    /// answer, which uses bitvectors as well.) What every
    /// caller relies on instead is ADMISSIBILITY, exhaustively proved over the
    /// whole powerset: `QF_ABV` admits arrays and bitvectors, which is all this
    /// formula uses.
    #[test]
    fn test_select_logic_array_bv_is_qf_abv() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "mem".into(),
                Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
            )),
            Box::new(bv_var("addr", 32)),
        );
        assert_eq!(select_logic(&f), "QF_ABV");
        // The pure bitvector fragment keeps its precise name.
        assert_eq!(
            select_logic(
                &Formula::BvULt(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32,)
            ),
            "QF_BV"
        );
    }

    /// LEVER C, CLOSED 2026-09-18. Arrays + bitvectors + integers used to take
    /// `ALL` for want of any name; `QF_AUFBVLIA` is the narrowest SMT-LIB name
    /// for that mix, so the answer is now a real name. The six names of the
    /// same class that were held out — because ay's IN-PROCESS parser refuses
    /// them — are rows now too: that parser is a property of ONE lane and is
    /// handled there, by `trust_router::in_process_ay_backend::
    /// native_lane_logic`, not by shrinking this table. None of them wins this
    /// selection, which is why the expectation below is unchanged.
    #[test]
    fn test_select_logic_array_bv_int_is_qf_aufbvlia() {
        let f = Formula::And(vec![
            Formula::Select(
                Box::new(Formula::Var(
                    "mem".into(),
                    Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
                )),
                Box::new(bv_var("addr", 32)),
            ),
            Formula::Gt(Box::new(var("len")), Box::new(Formula::Int(0))),
        ]);
        assert_eq!(select_logic(&f), "QF_AUFBVLIA");
    }

    /// Lever A, RE-POINTED 2026-09-18: a datatype-sorted variable — whether a
    /// full definition or a by-name recursive back-edge — must select a
    /// DATATYPE-CAPABLE logic, never a scalar-only one that would reject the
    /// declaration. It used to be `ALL` for all three shapes; it is now the
    /// narrowest SMT-LIB `*DT*` name, and every such name still routes through
    /// ay's `parse_logic` to `Logic::All` (`contains("DT")`), so nothing about
    /// the solve changed. An ARRAY-borne datatype is the exception and still
    /// takes `ALL`: the `A`-leading `DT` names have no [S1] declaration to cite
    /// for their array fragment.
    #[test]
    fn test_select_logic_datatype_var_is_datatype_capable() {
        let by_name = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), by_name.clone())),
            Box::new(Formula::Var("e".into(), by_name.clone())),
        );
        assert_eq!(select_logic(&f), "QF_DT");

        // A full definition, and a datatype nested behind an Array, both count.
        let full = Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), by_name.clone()), ("x".into(), by_name)]),
            ],
        };
        let g = Formula::Eq(
            Box::new(Formula::Var("e".into(), full.clone())),
            Box::new(Formula::Var("e".into(), full.clone())),
        );
        // The FULL definition names a `(_ BitVec 32)` field, and
        // `logic_lattice::sort_theories` follows a datatype into its
        // constructors' field sorts — it has to, because `declare-datatype`
        // writes every one of them into the transcript — so this record is
        // `{Datatypes, BitVectors}`.
        assert_eq!(select_logic(&g), "QF_UFBVDT");

        // A datatype nested behind an Array carries `ARRAYS` too, and no
        // `A`-leading `DT` name is attested well enough to claim it, so this
        // one is still `ALL` — the deliberate gap, not an oversight.
        let arr = Sort::Array(Box::new(Sort::Int), Box::new(full));
        let h = Formula::Eq(
            Box::new(Formula::Var("m".into(), arr.clone())),
            Box::new(Formula::Var("m".into(), arr)),
        );
        assert_eq!(select_logic(&h), "ALL");
    }

    /// The datatype surface is bigger than `Var`/`SymVar`. A GROUND constructor
    /// term, a selector application and a constructor tester each carry
    /// datatype content that no variable mentions, so a `Var`-only rule picked
    /// `QF_LIA`/`QF_BV` for them — a logic that does not admit datatypes.
    #[test]
    fn test_select_logic_ctor_sel_is_ctor_without_datatype_var_is_datatype_capable() {
        let expr = Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![("Const".into(), vec![("c".into(), Sort::BitVec(32))])],
        };

        // (= (Const #x00000001) (Const #x00000001)) — no free var at all.
        let ctor = Formula::Ctor {
            ctor: "Const".into(),
            args: vec![Formula::BitVec { value: 1, width: 32 }],
            sort: expr,
        };
        let f = Formula::Eq(Box::new(ctor.clone()), Box::new(ctor));
        assert_eq!(
            select_logic(&f),
            "QF_UFBVDT",
            "a ground Ctor term needs the datatype theory (and its field is a bitvector)"
        );

        // Sel / IsCtor over a NON-datatype-sorted variable: the datatype is
        // named by the node itself, so it must still select ALL.
        let n = Formula::Var("n".into(), Sort::Int);
        let sel = Formula::Eq(
            Box::new(Formula::Sel {
                datatype: "Expr".into(),
                field: "c".into(),
                field_sort: Sort::BitVec(32),
                arg: Box::new(n.clone()),
            }),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        );
        // `{Datatypes, BitVectors, Ints}`: the selector's FIELD sort is a
        // bitvector and its argument is an `Int`, and SMT-LIB's only names for
        // that mix are the `A`-leading `AUFBVDT*` ones this table declines to
        // claim — so the honest answer stays `ALL`.
        assert_eq!(select_logic(&sel), "ALL", "a selector application ranges over a datatype");

        let is_ctor =
            Formula::IsCtor { datatype: "Expr".into(), ctor: "Const".into(), arg: Box::new(n) };
        assert_eq!(
            select_logic(&is_ctor),
            "QF_UFDTLIA",
            "a constructor tester ranges over a datatype"
        );
    }

    /// A datatype reached ONLY through a quantifier binder still needs the
    /// datatype theory: the bound sorts are not `children()` edges, so the
    /// recursive walk never sees them via the body.
    #[test]
    fn test_select_logic_quantifier_bound_datatype_is_datatype_capable() {
        let expr = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Forall(
            vec![("e".into(), expr)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert_eq!(select_logic(&f), "UFDTLIA");
    }

    // --- collect_free_var_decls ---

    #[test]
    fn test_collect_free_var_decls_simple() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].0, "x");
        assert_eq!(decls[1].0, "y");
    }

    #[test]
    fn test_collect_free_var_decls_excludes_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Add(Box::new(var("x")), Box::new(var("y")))),
        );
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].0, "y");
    }

    #[test]
    fn test_collect_free_var_decls_mixed_sorts() {
        let f = Formula::And(vec![
            Formula::Var("flag".into(), Sort::Bool),
            var("count"),
            bv_var("bits", 32),
        ]);
        let decls: Vec<_> = collect_free_var_decls(&f).into_iter().collect();
        assert_eq!(decls.len(), 3);
        assert_eq!(decls[0].0, "bits");
        assert_eq!(decls[1].0, "count");
        assert_eq!(decls[2].0, "flag");
    }

    // --- infer_sort ---

    /// A `zero | succ(pred: Level)` datatype, fields spelled by-name as
    /// trust-ir-contract cuts them.
    fn level_sort() -> Sort {
        let by_name = Sort::Datatype { name: "Level".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), Vec::new()),
                ("succ".into(), vec![("pred".into(), by_name)]),
            ],
        }
    }

    /// Datatype terms infer the sort they CARRY, never the `Int` wildcard:
    /// `succ(l)` is `Level`, `pred(succ l)` is the field sort, `is_succ(x)`
    /// and an opaque `Pred` are `Bool`, and an `FnApp` is its declared result
    /// sort. The equations a recursive-datatype lane emits therefore compare
    /// two operands of ONE inferred sort, exactly as `check_formula_sort`
    /// already judged them.
    #[test]
    fn test_infer_sort_datatype_terms_carry_their_sort() {
        let level = level_sort();
        let l = Formula::Var("l".into(), level.clone());
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level.clone() };
        let pred = |a: Formula| Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: Sort::Datatype { name: "Level".into(), constructors: Vec::new() },
            arg: Box::new(a),
        };
        let is_succ = |a: Formula| Formula::IsCtor {
            datatype: "Level".into(),
            ctor: "succ".into(),
            arg: Box::new(a),
        };

        assert_eq!(infer_sort(&succ(l.clone())), level);
        assert_eq!(
            infer_sort(&pred(succ(l.clone()))),
            Sort::Datatype { name: "Level".into(), constructors: Vec::new() }
        );
        assert_eq!(infer_sort(&is_succ(l.clone())), Sort::Bool);
        assert_eq!(infer_sort(&Formula::Pred("p".into(), vec![Formula::Int(1)])), Sort::Bool);
        assert_eq!(
            infer_sort(&Formula::FnApp {
                func: "f".into(),
                args: vec![l.clone()],
                sort: Sort::BitVec(8)
            }),
            Sort::BitVec(8)
        );

        // The three equation shapes: each is a well-sorted predicate.
        for eq in [
            Formula::Eq(Box::new(succ(l.clone())), Box::new(l.clone())),
            Formula::Eq(Box::new(pred(succ(l.clone()))), Box::new(l.clone())),
            Formula::Eq(Box::new(is_succ(l.clone())), Box::new(Formula::Bool(true))),
        ] {
            assert_eq!(check_formula_sort(&eq), Ok(Sort::Bool), "{eq:?}");
            assert_eq!(infer_sort(&eq), Sort::Bool, "{eq:?}");
        }
        // `pred(succ l)` is spelled by-name while `l` carries the full
        // definition. `Sort` equality is structural, so the two INFERRED sorts
        // differ as values — but they AGREE (one datatype, `Level`), which is
        // what a mismatch pre-check must ask.
        let by_name = infer_sort(&pred(l.clone()));
        assert_ne!(by_name, level);
        assert!(sorts_agree(&by_name, &level));
        assert!(sorts_agree(&level, &by_name));

        // A GENUINE mismatch is still one: `Int` vs `Level`, and two
        // different datatypes.
        let bad = Formula::Eq(Box::new(Formula::Int(0)), Box::new(l.clone()));
        assert!(check_formula_sort(&bad).is_err());
        assert!(!sorts_agree(&infer_sort(&Formula::Int(0)), &infer_sort(&l)));
        let other = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        assert!(!sorts_agree(&other, &level));
        assert!(
            check_formula_sort(&Formula::Eq(
                Box::new(Formula::Var("e".into(), other)),
                Box::new(l.clone())
            ))
            .is_err()
        );
    }

    /// The vcgen induction-step shape: the pattern binder `__fld_Succ_0`
    /// carries the by-name `Level`, the IH variable the full definition, and
    /// the two are equated. The checker must judge that ONE sort, and its
    /// verdict on the equation must be the definitional (full) sort so a
    /// consumer can declare it.
    #[test]
    fn check_formula_sort_agrees_by_name_and_full_datatype_spellings() {
        let level = level_sort();
        let by_name = Sort::Datatype { name: "Level".into(), constructors: Vec::new() };
        let fld = Formula::Var("__fld_Succ_0".into(), by_name.clone());
        let ih = Formula::Var("__ih0".into(), level.clone());
        assert_eq!(
            check_formula_sort(&Formula::Eq(Box::new(ih.clone()), Box::new(fld.clone()))),
            Ok(Sort::Bool)
        );
        // `Ite` reports the definitional spelling whichever side carries it.
        let cond = Formula::Var("c".into(), Sort::Bool);
        for (then_, else_) in [(ih.clone(), fld.clone()), (fld.clone(), ih.clone())] {
            let ite = Formula::Ite(Box::new(cond.clone()), Box::new(then_), Box::new(else_));
            assert_eq!(check_formula_sort(&ite), Ok(level.clone()));
        }
        // Array element positions agree the same way.
        let arr =
            Formula::Var("a".into(), Sort::Array(Box::new(Sort::Int), Box::new(by_name.clone())));
        let store = Formula::Store(Box::new(arr), Box::new(Formula::Int(0)), Box::new(ih.clone()));
        assert!(check_formula_sort(&store).is_ok());
        // A different datatype name is still refused.
        let expr = Formula::Var(
            "e".into(),
            Sort::Datatype { name: "Expr".into(), constructors: Vec::new() },
        );
        assert!(check_formula_sort(&Formula::Eq(Box::new(ih), Box::new(expr))).is_err());
    }

    #[test]
    fn test_infer_sort_literals() {
        assert_eq!(infer_sort(&Formula::Bool(true)), Sort::Bool);
        assert_eq!(infer_sort(&Formula::Int(42)), Sort::Int);
        assert_eq!(infer_sort(&Formula::UInt(100)), Sort::Int);
        assert_eq!(infer_sort(&Formula::BitVec { value: 255, width: 8 }), Sort::BitVec(8));
    }

    #[test]
    fn test_infer_sort_boolean_ops() {
        assert_eq!(infer_sort(&Formula::Not(Box::new(Formula::Bool(true)))), Sort::Bool);
        assert_eq!(
            infer_sort(&Formula::And(vec![
                Formula::Var("a".into(), Sort::Bool),
                Formula::Var("b".into(), Sort::Bool),
            ])),
            Sort::Bool
        );
        assert_eq!(infer_sort(&Formula::Eq(Box::new(var("x")), Box::new(var("y")))), Sort::Bool);
    }

    #[test]
    fn test_infer_sort_arithmetic() {
        assert_eq!(infer_sort(&Formula::Add(Box::new(var("x")), Box::new(var("y")))), Sort::Int);
    }

    #[test]
    fn test_infer_sort_bv_ops() {
        assert_eq!(
            infer_sort(&Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32)),
            Sort::BitVec(32)
        );
    }

    #[test]
    fn test_infer_sort_ite_follows_then_branch() {
        let ite = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(bv_var("x", 64)),
            Box::new(bv_var("y", 64)),
        );
        assert_eq!(infer_sort(&ite), Sort::BitVec(64));
    }

    #[test]
    fn test_infer_sort_quantifiers_are_bool() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Ge(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(infer_sort(&f), Sort::Bool);
    }

    #[test]
    fn test_infer_sort_array_select() {
        let arr = Formula::Var(
            "arr".into(),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(32))),
        );
        let sel = Formula::Select(Box::new(arr), Box::new(Formula::Int(0)));
        assert_eq!(infer_sort(&sel), Sort::BitVec(32));
    }

    // --- split_top_level ---

    #[test]
    fn test_split_top_level_simple_tokens() {
        assert_eq!(split_top_level("and a b c"), vec!["and", "a", "b", "c"]);
    }

    #[test]
    fn test_split_top_level_nested_parens() {
        assert_eq!(split_top_level("and (> x 0) (< y 10)"), vec!["and", "(> x 0)", "(< y 10)"]);
    }

    #[test]
    fn test_split_top_level_empty() {
        assert!(split_top_level("").is_empty());
    }

    #[test]
    fn test_split_top_level_single_atom() {
        assert_eq!(split_top_level("x"), vec!["x"]);
    }

    #[test]
    fn test_split_top_level_deeply_nested() {
        assert_eq!(split_top_level("+ (f (g x)) y"), vec!["+", "(f (g x))", "y"]);
    }

    // --- FloatingPoint theory ---

    use crate::RoundingMode;

    fn fp_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Float { eb: 11, sb: 53 })
    }

    #[test]
    fn test_select_logic_pure_fp_is_qf_fp() {
        let f = Formula::FpLt(Box::new(fp_var("x")), Box::new(fp_var("y")));
        assert_eq!(select_logic(&f), "QF_FP");
    }

    #[test]
    fn test_select_logic_fp_op_without_fp_var_is_qf_fp() {
        let f = Formula::FpIsNaN(Box::new(Formula::FpNaN { eb: 11, sb: 53 }));
        assert_eq!(select_logic(&f), "QF_FP");
    }

    /// FLOATING POINT MIXED WITH BITVECTORS HEADS `QF_BVFP`, the SMT-LIB name
    /// for exactly that combined fragment.
    ///
    /// It answered `ALL` until the SMT-LIB name audit, for want of a row rather
    /// than for want of a name: `QF_BVFP` is in the library release and is the
    /// fragment SMT-LIB puts the `to_fp`-from-bitvector form in, which is why
    /// `logic_lattice::node_theories` charges BOTH bits on an `FpConst`. `ALL`
    /// was sound — it admits strictly more — but it sent every FP formula that
    /// so much as mentions a bitvector to the top of the lattice.
    ///
    /// The set that still takes `ALL` is FP mixed with INTEGERS: every SMT-LIB
    /// name admitting both also admits datatypes, which Lever A routes to `ALL`
    /// anyway. That is pinned here beside the BV case so the two are not
    /// confused for one rule.
    #[test]
    fn test_select_logic_fp_plus_bv_is_qf_bvfp() {
        let f = Formula::And(vec![
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::BvULt(Box::new(bv_var("b", 64)), Box::new(bv_var("c", 64)), 64),
        ]);
        assert_eq!(select_logic(&f), "QF_BVFP");

        let with_int = Formula::And(vec![
            f,
            Formula::Gt(Box::new(Formula::Var("n".into(), Sort::Int)), Box::new(Formula::Int(0))),
        ]);
        assert_eq!(
            select_logic(&with_int),
            "ALL",
            "SMT-LIB names no float+integer logic outside the datatype family"
        );
    }

    #[test]
    fn test_infer_sort_fp_arithmetic_is_float() {
        let add = Formula::FpAdd(
            Box::new(Formula::FpRoundingMode(RoundingMode::RNE)),
            Box::new(fp_var("x")),
            Box::new(fp_var("y")),
        );
        assert_eq!(infer_sort(&add), Sort::Float { eb: 11, sb: 53 });
    }

    #[test]
    fn test_infer_sort_fp_const_and_comparisons() {
        assert_eq!(
            infer_sort(&Formula::FpConst { bits: 0, eb: 8, sb: 24 }),
            Sort::Float { eb: 8, sb: 24 }
        );
        assert_eq!(
            infer_sort(&Formula::FpLe(Box::new(fp_var("x")), Box::new(fp_var("y")))),
            Sort::Bool
        );
        assert_eq!(infer_sort(&Formula::FpRoundingMode(RoundingMode::RTZ)), Sort::RoundingMode);
    }

    #[test]
    fn float_ordering_comparisons_are_bool_sorted() {
        // The canonicalized magnitude-contract shape: a Float-sorted var vs a
        // binary64 literal. Rejecting this silently degraded EVERY float
        // contract to the caller-side Bool(false) fallback (round-12).
        let var = Formula::Var("self.0".into(), Sort::Float { eb: 11, sb: 53 });
        let lit = Formula::FpConst { bits: 1.0e150_f64.to_bits().into(), eb: 11, sb: 53 };
        for f in [
            Formula::Le(Box::new(var.clone()), Box::new(lit.clone())),
            Formula::Ge(Box::new(var.clone()), Box::new(lit.clone())),
            Formula::Lt(Box::new(lit.clone()), Box::new(var.clone())),
            Formula::Gt(Box::new(lit.clone()), Box::new(var.clone())),
        ] {
            assert_eq!(check_formula_sort(&f), Ok(Sort::Bool), "{f:?}");
        }
        // Mixed sorts and differing float formats still reject.
        let int = Formula::Int(1);
        assert!(check_formula_sort(&Formula::Le(Box::new(var.clone()), Box::new(int))).is_err());
        let f32_var = Formula::Var("x".into(), Sort::Float { eb: 8, sb: 24 });
        assert!(
            check_formula_sort(&Formula::Le(Box::new(f32_var), Box::new(lit))).is_err(),
            "differing float formats must not compare"
        );
    }
}

/// The `Real` sort and the exact-rational literal: the QF_LRA fragment a
/// ny-cert Farkas system lowers to. The rules that matter for soundness are
/// the NEGATIVE ones — a real-valued atom must never be accepted as an
/// integer one, and vice versa — so each positive case has its mixed twin.
#[cfg(test)]
mod real_sort_tests {
    use super::*;

    fn rv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.into(), Sort::Real))
    }
    fn iv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.into(), Sort::Int))
    }
    fn q(num: &str, den: &str) -> Box<Formula> {
        Box::new(Formula::rat(num, den).expect("canonical rational"))
    }

    #[test]
    fn rational_literal_is_real_sorted_never_int() {
        assert_eq!(check_formula_sort(&q("1", "2")), Ok(Sort::Real));
        assert_eq!(infer_sort(&q("1", "2")), Sort::Real);
        assert_eq!(check_formula_sort(&Formula::rat_from_int(3)), Ok(Sort::Real));
        assert_ne!(check_formula_sort(&Formula::rat_from_int(3)), Ok(Sort::Int));
    }

    #[test]
    fn real_ordering_and_linear_arithmetic_are_well_sorted() {
        // (1/2)·x + y ≤ 7/3  and  x < 0  and  -x ≥ y  — the ny-cert shapes.
        let lhs = Formula::Add(Box::new(Formula::Mul(q("1", "2"), rv("x"))), rv("y"));
        assert_eq!(check_formula_sort(&lhs), Ok(Sort::Real));
        assert_eq!(infer_sort(&lhs), Sort::Real);
        let atom = Formula::Le(Box::new(lhs), q("7", "3"));
        assert_eq!(check_formula_sort(&atom), Ok(Sort::Bool));
        assert_eq!(check_formula_sort(&Formula::Lt(rv("x"), q("0", "1"))), Ok(Sort::Bool));
        assert_eq!(
            check_formula_sort(&Formula::Ge(Box::new(Formula::Neg(rv("x"))), rv("y"))),
            Ok(Sort::Bool)
        );
        assert_eq!(infer_sort(&Formula::Neg(rv("x"))), Sort::Real);
        assert_eq!(infer_sort(&Formula::Sub(rv("x"), rv("y"))), Sort::Real);
        // Int arithmetic is byte-for-byte unchanged.
        assert_eq!(
            check_formula_sort(&Formula::Add(iv("a"), Box::new(Formula::Int(1)))),
            Ok(Sort::Int)
        );
        assert_eq!(infer_sort(&Formula::Add(iv("a"), Box::new(Formula::Int(1)))), Sort::Int);
    }

    #[test]
    fn mixed_int_and_real_operands_are_rejected_not_coerced() {
        // An Int VARIABLE against a real term: which domain does the atom range
        // over? Refuse rather than guess.
        assert!(check_formula_sort(&Formula::Le(iv("n"), rv("x"))).is_err());
        assert!(check_formula_sort(&Formula::Lt(rv("x"), iv("n"))).is_err());
        assert!(check_formula_sort(&Formula::Add(iv("n"), rv("x"))).is_err());
        assert!(check_formula_sort(&Formula::Mul(rv("x"), iv("n"))).is_err());
        // An Int LITERAL is not silently promoted either: producers spell an
        // integer constant in a Real position as `Formula::Rat`.
        assert!(check_formula_sort(&Formula::Le(rv("x"), Box::new(Formula::Int(1)))).is_err());
        assert!(check_formula_sort(&Formula::Le(iv("n"), q("1", "1"))).is_err());
        // `infer_sort` never reports an ill-sorted predicate as Bool.
        assert_eq!(infer_sort(&Formula::Le(iv("n"), rv("x"))), Sort::Int);
    }

    #[test]
    fn truncating_division_has_no_real_meaning() {
        assert!(check_formula_sort(&Formula::Div(rv("x"), q("2", "1"))).is_err());
        assert!(check_formula_sort(&Formula::Rem(rv("x"), q("2", "1"))).is_err());
    }

    #[test]
    fn real_formulas_select_the_reals_logics() {
        let pure = Formula::And(vec![
            Formula::Le(Box::new(Formula::Mul(q("1", "2"), rv("x"))), q("1", "1")),
            Formula::Ge(rv("x"), q("3", "1")),
        ]);
        assert_eq!(select_logic(&pure), "QF_LRA");
        let mixed = Formula::And(vec![
            Formula::Le(rv("x"), q("1", "1")),
            Formula::Le(iv("n"), Box::new(Formula::Int(4))),
        ]);
        assert_eq!(select_logic(&mixed), "QF_LIRA");
        let quantified = Formula::Forall(
            vec![("x".into(), Sort::Real)],
            Box::new(Formula::Le(rv("x"), rv("x"))),
        );
        // QUANTIFIED reals take `LRA`, the name that says exactly that. A
        // previous revision answered `LIRA` — which admits reals, so it was
        // sound — because a fully monotone table cannot hold both `LRA` and
        // `LIA` (they would have to meet at "quantifiers alone", which no
        // SMT-LIB name spells). Monotonicity is no longer claimed, so the
        // precise name is back; `LRA` promises no integer theory the query
        // does not use.
        assert_eq!(select_logic(&quantified), "LRA");
        // Int-only stays QF_LIA — the Real lever must not touch it.
        assert_eq!(select_logic(&Formula::Le(iv("n"), Box::new(Formula::Int(4)))), "QF_LIA");
    }
}
