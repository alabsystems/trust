// trust-types/smt_logic.rs: Canonical SMT-LIB2 logic selection, free variable
// collection, and sort inference for Formula.
//
// Consolidated from trust_vcgen/smtlib2.rs, trust_vcgen/simplify_equivalence.rs,
// and trust-proof-cert/smt_equivalence.rs. This is the single authoritative location
// for these formula-level SMT utilities.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

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

fn expect_sort(
    operator: &'static str,
    actual: Sort,
    expected: Sort,
) -> Result<(), FormulaSortError> {
    if actual == expected {
        Ok(())
    } else {
        Err(FormulaSortError::Expected { operator, expected, actual })
    }
}

fn same_sort(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
) -> Result<Sort, FormulaSortError> {
    let left = check_formula_sort(left)?;
    let right = check_formula_sort(right)?;
    if left == right {
        Ok(left)
    } else {
        Err(FormulaSortError::Mismatch { operator, left, right })
    }
}

fn int_binary(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
) -> Result<Sort, FormulaSortError> {
    expect_sort(operator, check_formula_sort(left)?, Sort::Int)?;
    expect_sort(operator, check_formula_sort(right)?, Sort::Int)?;
    Ok(Sort::Int)
}

fn bv_operand(
    operator: &'static str,
    operand: &Formula,
    width: u32,
) -> Result<(), FormulaSortError> {
    match check_formula_sort(operand)? {
        Sort::BitVec(actual) if actual == width => Ok(()),
        Sort::BitVec(actual) => Err(FormulaSortError::BitWidth {
            operator,
            declared: width,
            actual,
        }),
        actual => Err(FormulaSortError::Expected {
            operator,
            expected: Sort::BitVec(width),
            actual,
        }),
    }
}

fn bv_binary(
    operator: &'static str,
    left: &Formula,
    right: &Formula,
    width: u32,
    result: Sort,
) -> Result<Sort, FormulaSortError> {
    bv_operand(operator, left, width)?;
    bv_operand(operator, right, width)?;
    Ok(result)
}

fn float_operand(
    operator: &'static str,
    operand: &Formula,
    expected: &Sort,
) -> Result<(), FormulaSortError> {
    expect_sort(operator, check_formula_sort(operand)?, expected.clone())
}

/// Recursively infer and validate the sort of every formula node.
///
/// Unlike [`infer_sort`], this exposes malformed children as a structured
/// error.  It is the required boundary for accepting source contracts,
/// reusable summaries, or other externally supplied formulas.
pub fn check_formula_sort(formula: &Formula) -> Result<Sort, FormulaSortError> {
    match formula {
        Formula::Bool(_) => Ok(Sort::Bool),
        Formula::Int(_) | Formula::UInt(_) => Ok(Sort::Int),
        Formula::BitVec { width, .. } => Ok(Sort::BitVec(*width)),
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => Ok(sort.clone()),

        Formula::Not(inner) => {
            expect_sort("not", check_formula_sort(inner)?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                expect_sort("Boolean connective", check_formula_sort(item)?, Sort::Bool)?;
            }
            Ok(Sort::Bool)
        }
        Formula::Implies(left, right) => {
            expect_sort("implication", check_formula_sort(left)?, Sort::Bool)?;
            expect_sort("implication", check_formula_sort(right)?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        Formula::Eq(left, right) => {
            same_sort("equality", left, right)?;
            Ok(Sort::Bool)
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
            let left_sort = check_formula_sort(left)?;
            let right_sort = check_formula_sort(right)?;
            match (&left_sort, &right_sort) {
                (Sort::Int, Sort::Int) => Ok(Sort::Bool),
                (Sort::Float { eb: le, sb: ls }, Sort::Float { eb: re, sb: rs })
                    if le == re && ls == rs =>
                {
                    Ok(Sort::Bool)
                }
                _ => {
                    expect_sort("ordering comparison", left_sort, Sort::Int)?;
                    expect_sort("ordering comparison", right_sort, Sort::Int)?;
                    Ok(Sort::Bool)
                }
            }
        }

        Formula::Add(left, right)
        | Formula::Sub(left, right)
        | Formula::Mul(left, right)
        | Formula::Div(left, right)
        | Formula::Rem(left, right) => int_binary("integer arithmetic", left, right),
        Formula::Neg(inner) => {
            expect_sort("integer negation", check_formula_sort(inner)?, Sort::Int)?;
            Ok(Sort::Int)
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
        | Formula::BvAShr(left, right, width) => bv_binary(
            "bitvector binary operation",
            left,
            right,
            *width,
            Sort::BitVec(*width),
        ),
        Formula::BvNot(inner, width) => {
            bv_operand("bitvector not", inner, *width)?;
            Ok(Sort::BitVec(*width))
        }
        Formula::BvULt(left, right, width)
        | Formula::BvULe(left, right, width)
        | Formula::BvSLt(left, right, width)
        | Formula::BvSLe(left, right, width) => bv_binary(
            "bitvector comparison",
            left,
            right,
            *width,
            Sort::Bool,
        ),
        Formula::BvToInt(inner, width, _) => {
            bv_operand("bitvector-to-int", inner, *width)?;
            Ok(Sort::Int)
        }
        Formula::IntToBv(inner, width) => {
            expect_sort("int-to-bitvector", check_formula_sort(inner)?, Sort::Int)?;
            Ok(Sort::BitVec(*width))
        }
        Formula::BvExtract { inner, high, low } => {
            let Sort::BitVec(width) = check_formula_sort(inner)? else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector extract",
                    expected: Sort::BitVec(high.saturating_add(1)),
                    actual: check_formula_sort(inner)?,
                });
            };
            if high < low || *high >= width {
                return Err(FormulaSortError::InvalidExtract {
                    high: *high,
                    low: *low,
                    width,
                });
            }
            Ok(Sort::BitVec(high - low + 1))
        }
        Formula::BvConcat(left, right) => {
            let Sort::BitVec(left_width) = check_formula_sort(left)? else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector concat",
                    expected: Sort::BitVec(1),
                    actual: check_formula_sort(left)?,
                });
            };
            let Sort::BitVec(right_width) = check_formula_sort(right)? else {
                return Err(FormulaSortError::Expected {
                    operator: "bitvector concat",
                    expected: Sort::BitVec(1),
                    actual: check_formula_sort(right)?,
                });
            };
            Ok(Sort::BitVec(left_width.saturating_add(right_width)))
        }
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => {
            let actual = check_formula_sort(inner)?;
            if let Sort::BitVec(width) = actual {
                Ok(Sort::BitVec(width.saturating_add(*extra)))
            } else {
                Err(FormulaSortError::Expected {
                    operator: "bitvector extension",
                    expected: Sort::BitVec(1),
                    actual,
                })
            }
        }

        Formula::FpConst { eb, sb, .. }
        | Formula::FpNaN { eb, sb }
        | Formula::FpInf { eb, sb, .. }
        | Formula::FpZero { eb, sb, .. } => Ok(Sort::Float { eb: *eb, sb: *sb }),
        Formula::FpRoundingMode(_) => Ok(Sort::RoundingMode),
        Formula::FpFromBits { bits, eb, sb } => {
            expect_sort(
                "float-from-bits",
                check_formula_sort(bits)?,
                Sort::BitVec(eb.saturating_add(*sb)),
            )?;
            Ok(Sort::Float { eb: *eb, sb: *sb })
        }
        Formula::FpToIeeeBv(inner) => match check_formula_sort(inner)? {
            Sort::Float { eb, sb } => Ok(Sort::BitVec(eb.saturating_add(sb))),
            actual => Err(FormulaSortError::Expected {
                operator: "float-to-bits",
                expected: Sort::Float { eb: 8, sb: 24 },
                actual,
            }),
        },
        Formula::FpAdd(round, left, right)
        | Formula::FpSub(round, left, right)
        | Formula::FpMul(round, left, right)
        | Formula::FpDiv(round, left, right) => {
            expect_sort("floating arithmetic", check_formula_sort(round)?, Sort::RoundingMode)?;
            let sort = same_sort("floating arithmetic", left, right)?;
            if matches!(sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating arithmetic",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                })
            }
        }
        Formula::FpFma(round, first, second, third) => {
            expect_sort("floating fused multiply-add", check_formula_sort(round)?, Sort::RoundingMode)?;
            let sort = same_sort("floating fused multiply-add", first, second)?;
            float_operand("floating fused multiply-add", third, &sort)?;
            if matches!(sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating fused multiply-add",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                })
            }
        }
        Formula::FpSqrt(round, inner) => {
            expect_sort("floating square root", check_formula_sort(round)?, Sort::RoundingMode)?;
            let sort = check_formula_sort(inner)?;
            if matches!(sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating square root",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                })
            }
        }
        Formula::FpRem(left, right)
        | Formula::FpMin(left, right)
        | Formula::FpMax(left, right) => {
            let sort = same_sort("floating binary operation", left, right)?;
            if matches!(sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating binary operation",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                })
            }
        }
        Formula::FpNeg(inner) | Formula::FpAbs(inner) => {
            let sort = check_formula_sort(inner)?;
            if matches!(sort, Sort::Float { .. }) {
                Ok(sort)
            } else {
                Err(FormulaSortError::Expected {
                    operator: "floating unary operation",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                })
            }
        }
        Formula::FpEq(left, right)
        | Formula::FpLt(left, right)
        | Formula::FpLe(left, right)
        | Formula::FpGt(left, right)
        | Formula::FpGe(left, right) => {
            let sort = same_sort("floating comparison", left, right)?;
            if !matches!(sort, Sort::Float { .. }) {
                return Err(FormulaSortError::Expected {
                    operator: "floating comparison",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                });
            }
            Ok(Sort::Bool)
        }
        Formula::FpIsNaN(inner)
        | Formula::FpIsInfinite(inner)
        | Formula::FpIsZero(inner)
        | Formula::FpIsNormal(inner)
        | Formula::FpIsSubnormal(inner)
        | Formula::FpIsNegative(inner)
        | Formula::FpIsPositive(inner) => {
            let sort = check_formula_sort(inner)?;
            if !matches!(sort, Sort::Float { .. }) {
                return Err(FormulaSortError::Expected {
                    operator: "floating classification",
                    expected: Sort::Float { eb: 8, sb: 24 },
                    actual: sort,
                });
            }
            Ok(Sort::Bool)
        }

        Formula::Ite(condition, then_branch, else_branch) => {
            expect_sort("if-then-else condition", check_formula_sort(condition)?, Sort::Bool)?;
            same_sort("if-then-else", then_branch, else_branch)
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            expect_sort("quantifier body", check_formula_sort(body)?, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        Formula::Select(array, index) => match check_formula_sort(array)? {
            Sort::Array(index_sort, element_sort) => {
                expect_sort("array select", check_formula_sort(index)?, *index_sort)?;
                Ok(*element_sort)
            }
            actual => Err(FormulaSortError::Expected {
                operator: "array select",
                expected: Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                actual,
            }),
        },
        Formula::Store(array, index, value) => match check_formula_sort(array)? {
            Sort::Array(index_sort, element_sort) => {
                expect_sort("array store index", check_formula_sort(index)?, (*index_sort).clone())?;
                expect_sort("array store value", check_formula_sort(value)?, (*element_sort).clone())?;
                Ok(Sort::Array(index_sort, element_sort))
            }
            actual => Err(FormulaSortError::Expected {
                operator: "array store",
                expected: Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
                actual,
            }),
        },
        Formula::Pred(_, arguments) => {
            for argument in arguments {
                check_formula_sort(argument)?;
            }
            Ok(Sort::Bool)
        }
        Formula::Ctor { args, sort, .. } | Formula::FnApp { args, sort, .. } => {
            for argument in args {
                check_formula_sort(argument)?;
            }
            Ok(sort.clone())
        }
        Formula::Sel { arg, field_sort, .. } => {
            check_formula_sort(arg)?;
            Ok(field_sort.clone())
        }
        Formula::IsCtor { arg, .. } => {
            check_formula_sort(arg)?;
            Ok(Sort::Bool)
        }
        #[allow(unreachable_patterns)]
        _ => Err(FormulaSortError::UnsupportedVariant),
    }
}

/// Select the appropriate SMT-LIB2 logic based on formula features.
///
/// Analyzes the formula to determine which theories are needed:
/// - `QF_LIA`: quantifier-free linear integer arithmetic (default)
/// - `QF_BV`: quantifier-free bitvectors
/// - `QF_ABV`: quantifier-free arrays + bitvectors
/// - `QF_ALIA`: quantifier-free arrays + linear integer arithmetic
/// - `ALIA`: arrays + linear integer arithmetic (with quantifiers)
/// - `LIA`: linear integer arithmetic (with quantifiers)
/// - `ALL`: when multiple complex theories are combined
#[must_use]
pub fn select_logic(formula: &Formula) -> &'static str {
    let mut has_bv = false;
    let mut has_array = false;
    let mut has_quantifier = false;
    let mut has_int = false;
    let mut has_fp = false;
    let mut has_datatype = false;

    formula.visit(&mut |f| match f {
        // Lever A: a datatype-sorted (or datatype-back-edge) variable needs the
        // datatype theory. `ALL` is a safe superset that admits datatypes plus
        // the BV/Int/UF scalar fields a recursive ADT's leaves produce; it only
        // widens the theory set and never changes a formula's models.
        Formula::Var(_, s) | Formula::SymVar(_, s) if s.contains_datatype() => has_datatype = true,
        // …but a variable is NOT the whole datatype surface. A GROUND
        // constructor term (`Ctor`) carries its datatype result sort, a
        // selector application (`Sel`) and a constructor tester (`IsCtor`) are
        // datatype-ranging BY CONSTRUCTION (their `datatype` field names the
        // sort), and an uninterpreted application (`FnApp`) can return one. A
        // formula whose only datatype content is such a term reaches no `Var`
        // at all, so keying on variables alone would pick a logic that does not
        // admit the datatype theory.
        Formula::Sel { .. } | Formula::IsCtor { .. } => has_datatype = true,
        Formula::Ctor { sort: s, .. } | Formula::FnApp { sort: s, .. }
            if s.contains_datatype() =>
        {
            has_datatype = true;
        }
        // FloatingPoint theory: any fp.* operator/literal or FP/RoundingMode var.
        Formula::Var(_, Sort::Float { .. } | Sort::RoundingMode)
        | Formula::SymVar(_, Sort::Float { .. } | Sort::RoundingMode) => has_fp = true,
        other if is_fp_op(other) => has_fp = true,
        Formula::BitVec { .. }
        | Formula::BvAdd(..)
        | Formula::BvSub(..)
        | Formula::BvMul(..)
        | Formula::BvUDiv(..)
        | Formula::BvSDiv(..)
        | Formula::BvURem(..)
        | Formula::BvSRem(..)
        | Formula::BvAnd(..)
        | Formula::BvOr(..)
        | Formula::BvXor(..)
        | Formula::BvNot(..)
        | Formula::BvShl(..)
        | Formula::BvLShr(..)
        | Formula::BvAShr(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::BvToInt(..)
        | Formula::IntToBv(..)
        | Formula::BvExtract { .. }
        | Formula::BvConcat(..)
        | Formula::BvZeroExt(..)
        | Formula::BvSignExt(..) => has_bv = true,
        Formula::Var(_, Sort::BitVec(_)) | Formula::SymVar(_, Sort::BitVec(_)) => has_bv = true,
        Formula::Select(..) | Formula::Store(..) => has_array = true,
        Formula::Var(_, Sort::Array(..)) | Formula::SymVar(_, Sort::Array(..)) => has_array = true,
        // A binder's sorts live in the binding LIST, which is not a `children()`
        // edge — so a datatype that appears only as a bound sort is invisible to
        // the recursive walk over the body.
        Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
            has_quantifier = true;
            if bindings.iter().any(|(_, s)| s.contains_datatype()) {
                has_datatype = true;
            }
        }
        Formula::Int(_) | Formula::UInt(_) => has_int = true,
        Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int) => has_int = true,
        Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Neg(..) => has_int = true,
        _ => {}
    });

    // Lever A: any datatype content -> `ALL` (admits datatypes + every scalar
    // theory). Checked first because it subsumes all the cases below.
    if has_datatype {
        return "ALL";
    }

    // FloatingPoint theory. Pure quantifier-free FP -> QF_FP; any mix with other
    // theories (notably the bitvector bridge that carries float bit-patterns, or
    // quantifiers) -> ALL, a safe superset, so this never under-approximates.
    if has_fp {
        if !has_quantifier && !has_array && !has_int && !has_bv {
            return "QF_FP";
        }
        return "ALL";
    }

    match (has_quantifier, has_array, has_bv, has_int) {
        // Trust: specific multi-theory logics before catch-all
        (false, true, true, false) => "QF_ABV",
        (_, true, true, _) | (_, _, true, true) => "ALL",
        (false, true, false, true) => "QF_ALIA",
        (true, true, false, true) => "ALIA",
        (false, false, true, false) => "QF_BV",
        (true, false, false, _) => "LIA",
        _ => "QF_LIA",
    }
}

/// Whether a formula node is a FloatingPoint-theory operator or literal.
/// Variables are excluded (their FP-ness is detected via their `Sort`).
fn is_fp_op(f: &Formula) -> bool {
    matches!(
        f,
        Formula::FpConst { .. }
            | Formula::FpNaN { .. }
            | Formula::FpInf { .. }
            | Formula::FpZero { .. }
            | Formula::FpRoundingMode(_)
            | Formula::FpAdd(..)
            | Formula::FpSub(..)
            | Formula::FpMul(..)
            | Formula::FpDiv(..)
            | Formula::FpFma(..)
            | Formula::FpSqrt(..)
            | Formula::FpRem(..)
            | Formula::FpNeg(..)
            | Formula::FpAbs(..)
            | Formula::FpMin(..)
            | Formula::FpMax(..)
            | Formula::FpEq(..)
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
            | Formula::FpIsPositive(..)
            | Formula::FpFromBits { .. }
            // `FpToIeeeBv` operates on an FP operand (FP->BV reinterpret); its
            // presence signals the FloatingPoint theory even though its RESULT
            // is a bitvector.
            | Formula::FpToIeeeBv(..)
    )
}

/// Collect all free variable declarations from a formula.
///
/// Returns a sorted `BTreeSet` of `(name, sort)` pairs for deterministic output.
/// Bound variables (from `Forall`/`Exists`) are excluded.
#[must_use]
pub fn collect_free_var_decls(formula: &Formula) -> BTreeSet<(String, Sort)> {
    let free = formula.free_variables();
    let mut decls = BTreeSet::new();

    formula.visit(&mut |f| {
        match f {
            Formula::Var(name, sort) if free.contains(name) => {
                decls.insert((name.clone(), sort.clone()));
            }
            // SymVar — resolve symbol to string for free var decl collection.
            Formula::SymVar(sym, sort) => {
                let name = sym.as_str().to_string();
                if free.contains(&name) {
                    decls.insert((name, sort.clone()));
                }
            }
            _ => {}
        }
    });

    decls
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
///
/// Defaults to `Sort::Int` for ambiguous cases.
#[must_use]
pub fn infer_sort(formula: &Formula) -> Sort {
    // Keep the long-standing total return type for broad solver plumbing, but
    // never report an ill-typed predicate as Boolean.  Callers that need the
    // diagnostic use `check_formula_sort`; legacy callers receive the
    // conservative non-predicate sentinel `Int` on any recursive error.
    if check_formula_sort(formula).is_err() {
        return Sort::Int;
    }
    match formula {
        // Literals
        Formula::Bool(_) => Sort::Bool,
        Formula::Int(_) | Formula::UInt(_) => Sort::Int,
        Formula::BitVec { width, .. } => Sort::BitVec(*width),

        // Variables carry their own sort
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => sort.clone(),

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
        | Formula::BvSLe(_, _, _) => Sort::Bool,

        // Integer arithmetic
        Formula::Add(_, _)
        | Formula::Sub(_, _)
        | Formula::Mul(_, _)
        | Formula::Div(_, _)
        | Formula::Rem(_, _)
        | Formula::Neg(_) => Sort::Int,

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
        | Formula::BvAShr(_, _, w) => Sort::BitVec(*w),

        // Bitvector conversions
        Formula::BvToInt(_, _, _) => Sort::Int,
        Formula::IntToBv(_, w) => Sort::BitVec(*w),
        Formula::BvExtract { high, low, .. } => Sort::BitVec(high - low + 1),
        Formula::BvConcat(a, b) => {
            let wa = match infer_sort(a) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            let wb = match infer_sort(b) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(wa + wb)
        }
        Formula::BvZeroExt(inner, extra) => {
            let base = match infer_sort(inner) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(base + extra)
        }
        Formula::BvSignExt(inner, extra) => {
            let base = match infer_sort(inner) {
                Sort::BitVec(w) => w,
                _ => 0,
            };
            Sort::BitVec(base + extra)
        }

        // FloatingPoint — literals/typed nodes carry their format directly.
        Formula::FpConst { eb, sb, .. }
        | Formula::FpNaN { eb, sb }
        | Formula::FpInf { eb, sb, .. }
        | Formula::FpZero { eb, sb, .. }
        | Formula::FpFromBits { eb, sb, .. } => Sort::Float { eb: *eb, sb: *sb },
        Formula::FpRoundingMode(_) => Sort::RoundingMode,
        // `(fp.to_ieee_bv <fp>)` yields an `(eb+sb)`-wide bitvector; recover the
        // format from the FP operand's sort. (The inverse of `FpFromBits`, whose
        // result is the Float sort.)
        Formula::FpToIeeeBv(a) => match infer_sort(a) {
            Sort::Float { eb, sb } => Sort::BitVec(eb + sb),
            _ => Sort::BitVec(64),
        },
        // FP arithmetic — recover the format from a float operand.
        Formula::FpAdd(_, a, _)
        | Formula::FpSub(_, a, _)
        | Formula::FpMul(_, a, _)
        | Formula::FpDiv(_, a, _)
        | Formula::FpFma(_, a, _, _)
        | Formula::FpSqrt(_, a) => infer_sort(a),
        Formula::FpRem(a, _)
        | Formula::FpMin(a, _)
        | Formula::FpMax(a, _)
        | Formula::FpNeg(a)
        | Formula::FpAbs(a) => infer_sort(a),
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
        | Formula::FpIsPositive(..) => Sort::Bool,

        // Conditional -- sort of the then-branch
        Formula::Ite(_, then_br, _) => infer_sort(then_br),

        // Quantifiers always produce Bool
        Formula::Forall(_, _) | Formula::Exists(_, _) => Sort::Bool,

        // Array operations
        Formula::Select(arr, _) => {
            if let Sort::Array(_, elem) = infer_sort(arr) {
                *elem
            } else {
                Sort::Int
            }
        }
        Formula::Store(arr, _, _) => infer_sort(arr),

        // Conservative fallback for future #[non_exhaustive] variants.
        #[allow(unreachable_patterns)]
        _ => Sort::Int,
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
    for (i, ch) in input.char_indices() {
        match ch {
            ' ' | '\t' | '\n' if depth == 0 => {
                if let Some(s) = start {
                    let token = &input[s..i];
                    if !token.trim().is_empty() {
                        parts.push(token);
                    }
                    start = None;
                }
            }
            '(' => {
                if start.is_none() {
                    start = Some(i);
                }
                depth += 1;
            }
            ')' => {
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

    #[test]
    fn test_select_logic_array_bv() {
        let f = Formula::Select(
            Box::new(Formula::Var(
                "mem".into(),
                Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
            )),
            Box::new(bv_var("addr", 32)),
        );
        assert_eq!(select_logic(&f), "QF_ABV");
    }

    #[test]
    fn test_select_logic_array_bv_int_is_all() {
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
        assert_eq!(select_logic(&f), "ALL");
    }

    /// Lever A: a datatype-sorted variable — whether a full definition or a
    /// by-name recursive back-edge — must select the datatype-capable `ALL`,
    /// never a scalar-only logic that would reject the declaration.
    #[test]
    fn test_select_logic_datatype_var_is_all() {
        let by_name = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), by_name.clone())),
            Box::new(Formula::Var("e".into(), by_name.clone())),
        );
        assert_eq!(select_logic(&f), "ALL");

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
        assert_eq!(select_logic(&g), "ALL");

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
    fn test_select_logic_ctor_sel_is_ctor_without_datatype_var_is_all() {
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
        assert_eq!(select_logic(&f), "ALL", "a ground Ctor term needs the datatype theory");

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
        assert_eq!(select_logic(&sel), "ALL", "a selector application ranges over a datatype");

        let is_ctor = Formula::IsCtor {
            datatype: "Expr".into(),
            ctor: "Const".into(),
            arg: Box::new(n),
        };
        assert_eq!(select_logic(&is_ctor), "ALL", "a constructor tester ranges over a datatype");
    }

    /// A datatype reached ONLY through a quantifier binder still needs the
    /// datatype theory: the bound sorts are not `children()` edges, so the
    /// recursive walk never sees them via the body.
    #[test]
    fn test_select_logic_quantifier_bound_datatype_is_all() {
        let expr = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Forall(
            vec![("e".into(), expr)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            )),
        );
        assert_eq!(select_logic(&f), "ALL");
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

    #[test]
    fn test_select_logic_fp_plus_bv_is_all() {
        let f = Formula::And(vec![
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::BvULt(Box::new(bv_var("b", 64)), Box::new(bv_var("c", 64)), 64),
        ]);
        assert_eq!(select_logic(&f), "ALL");
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
        assert_eq!(
            infer_sort(&Formula::FpRoundingMode(RoundingMode::RTZ)),
            Sort::RoundingMode
        );
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
