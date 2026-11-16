//! The one canonical query hash: a SHA-256 identity of a solver QUERY — every
//! assertion in scope at one check-sat — up to one consistent renaming of its
//! free variables.
//!
//! It lived in `trust-router`'s cross-function solver cache, whose only purpose
//! was to key replayed verdicts on it. That cache is gone (plan P4 / T4.2:
//! verdicts must not depend on the order in which functions filled a
//! process-wide map), so it lives here, beside the formula type, as the one
//! formula identity the toolchain has.
//!
//! It identifies formulas, not verdicts. A record that keys a verdict on it
//! (T12's obligation records) must hash every assertion the check-sat sees
//! (the common assertions and the function prefix as well as the VC), and must
//! bind the solver and encoding identity (the solver build, its options, the
//! logic and the encoding the assertions were lowered with) beside it. The API
//! takes the assertion set, not one formula, so that a VC formula cannot be
//! keyed alone by accident.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;
use crate::{Formula, Sort};

/// Reserved canonical-name prefix used by free-variable alpha-normalization.
///
/// Free variables are rewritten to `__trust_fv0`, `__trust_fv1`, ... in first
/// occurrence (structural pre-order) order. The prefix is deliberately long and
/// `trustc`-specific so it cannot collide with a real MIR-local (`_3`) or a
/// vcgen-synthesized symbol; if a source formula nevertheless already contains a
/// name with this prefix, normalization FAILS CLOSED (see
/// [`alpha_canonicalize_free_vars`]) rather than risk merging two distinct
/// variables onto one canonical name.
const FV_CANON_PREFIX: &str = "__trust_fv";

/// Deterministic SHA-256 identity (lowercase hex) of the query whose
/// assertions, in assertion order, are `assertions`.
///
/// # Soundness contract
///
/// Two queries share this hash **iff** their assertion sequences are
/// alpha-equivalent under ONE renaming: identical structure, assertion by
/// assertion, up to a single consistent bijective renaming of the free
/// variables across all of them (same constants, operators, widths, sorts, and
/// structure). A collision between non-equivalent queries would let one
/// query's record stand for the other's — a false proof wherever the hash is
/// used as a key.
///
/// The renaming is a renaming of the whole query, which is why the caller
/// passes every assertion in scope at the check-sat. `x < y` and `y < x` are
/// the same question when nothing else is asserted, and different questions
/// under an assertion that fixes `x`: hashed with that assertion they split,
/// hashed alone they collide. Passing a VC formula without the assertions it
/// is solved under (the subprocess session's common assertions and function
/// prefix) would therefore merge two different questions. The hash also says
/// nothing about how the query is solved: a verdict key binds the solver and
/// encoding identity beside it (module docs).
///
/// A conservative free-variable alpha-normalization
/// ([`alpha_canonicalize_free_vars`]) runs first, so two functions whose
/// queries are identical up to MIR-local renaming (`_0`/`_1` in `f` vs `g`)
/// share the hash. When normalization is not provably sound for a query (it
/// contains a quantifier, or already uses a reserved canonical name), the raw,
/// un-renamed query is hashed instead — that never over-merges. Correctness
/// over hit-rate: a missed merge only costs a re-solve; a wrong merge is
/// unsound.
///
/// The hash is over serde's exact structural representation of the canonical
/// query (the assertions as the children of one `And`, in order), not SMT-LIB
/// text. The SMT renderer deliberately omits some AST
/// payloads that a solver recovers from declarations or context; those
/// omissions are valid for printing but not for identity. Derived serialization
/// automatically covers every current and future formula variant and all of its
/// sort/width/format payloads. SHA-256 provides collision resistance to ~2^128.
/// See #692, #754.
///
/// # Errors
///
/// When the canonical query does not serialize. There is then no identity,
/// and a caller keys nothing on it (it never falls back to another spelling).
pub fn canonical_query_hash(assertions: &[&Formula]) -> Result<String, serde_json::Error> {
    let mut mapping: FxHashMap<&str, usize> = FxHashMap::default();
    let can_canonicalize = assertions
        .iter()
        .all(|&assertion| collect_free_var_mapping(assertion, &mut mapping));
    let mut writer = Sha256Writer(sha2::Sha256::new());
    if can_canonicalize && !mapping.is_empty() {
        let query = Formula::And(
            assertions
                .iter()
                .map(|&assertion| rewrite_free_vars(assertion.clone(), &mapping))
                .collect(),
        );
        serde_json::to_writer(&mut writer, &query)?;
    } else {
        #[derive(serde::Serialize)]
        struct BorrowedAndQuery<'a> {
            #[serde(rename = "And")]
            and: &'a [&'a Formula],
        }
        serde_json::to_writer(&mut writer, &BorrowedAndQuery { and: assertions })?;
    }
    use sha2::Digest;
    Ok(crate::digest::lowercase_hex(&writer.0.finalize()))
}

struct Sha256Writer(sha2::Sha256);

impl std::io::Write for Sha256Writer {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        use sha2::Digest;
        self.0.update(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn collect_free_var_mapping<'a>(
    formula: &'a Formula,
    mapping: &mut FxHashMap<&'a str, usize>,
) -> bool {
    let mut has_quantifier = false;
    let mut reserved_name_in_use = false;
    let _ = crate::all_formula_nodes(formula, &mut |f| {
        match f {
            Formula::Forall(..) | Formula::Exists(..) => has_quantifier = true,
            Formula::Var(name, _) => {
                if name.starts_with(FV_CANON_PREFIX) {
                    reserved_name_in_use = true;
                } else {
                    let next_idx = mapping.len();
                    mapping.entry(name.as_str()).or_insert(next_idx);
                }
            }
            Formula::SymVar(sym, _) => {
                let name = sym.as_str();
                if name.starts_with(FV_CANON_PREFIX) {
                    reserved_name_in_use = true;
                } else {
                    let next_idx = mapping.len();
                    mapping.entry(name).or_insert(next_idx);
                }
            }
            _ => {}
        }
        !has_quantifier && !reserved_name_in_use
    });
    !has_quantifier && !reserved_name_in_use
}

fn rewrite_free_vars(formula: Formula, mapping: &FxHashMap<&str, usize>) -> Formula {
    formula.map(&mut |node| match node {
        Formula::Var(name, sort) => rename_leaf(&name, sort, mapping),
        Formula::SymVar(sym, sort) => rename_leaf(sym.as_str(), sort, mapping),
        other => other,
    })
}

/// Alpha-normalize the **free** variables of a quantifier-free formula to a
/// canonical, position-determined order, or return `None` if it cannot do so
/// soundly.
///
/// MIR-locals (`_0`, `_1`, …) and most vcgen-synthesized operands appear in VC
/// formulas as *free* `Var`/`SymVar` leaves. Two functions can emit the same
/// obligation up to a consistent renaming of these locals (`_0 < _1` in `f` is
/// the same proof problem as `_3 < _7` in `g`). Renaming each distinct free
/// variable to `__trust_fvN` by first structural occurrence makes such
/// obligations share an identity.
///
/// # Why this is sound (and where it deliberately bails)
///
/// The returned formula must be alpha-EQUIVALENT to the input — its structural
/// encoding must equal another formula's *only* when the two are identical up
/// to a consistent **bijective** renaming of free variables. The transform
/// preserves that because:
///
/// * It is **quantifier-free**: if the formula contains any `Forall`/`Exists`,
///   it returns `None`. With no binders, every `Var`/`SymVar` leaf is free, so
///   it never needs binder-scope tracking and can never capture a bound
///   variable or treat a bound variable as free.
/// * The rename is a **bijection**: distinct source names map to distinct
///   `__trust_fvN` names (one entry per name in `mapping`, never merged), and
///   the numbering is injective.
/// * Numbering is by **first occurrence in a fixed structural pre-order**, the
///   same total order for any two alpha-equivalent formulas, so equivalent
///   inputs produce *identical* renamed forms, while any structural difference
///   (a constant, operator, width, sort, or shape) survives the rename.
/// * Sorts and all non-variable payload (widths, constants, predicate names)
///   are carried through unchanged by reusing `Formula::map`; only the *name*
///   of a free `Var`/`SymVar` is rewritten.
/// * If any source variable already uses the reserved [`FV_CANON_PREFIX`], it
///   returns `None`: a pre-existing `__trust_fvK` could otherwise alias a
///   generated name and merge two distinct variables. Fail closed.
fn alpha_canonicalize_free_vars(formula: &Formula) -> Option<Formula> {
    let mut mapping: FxHashMap<&str, usize> = FxHashMap::default();
    if !collect_free_var_mapping(formula, &mut mapping) {
        return None;
    }

    // Rewrite every free Var/SymVar leaf to its canonical Var, preserving sort.
    // SymVar is normalized to Var so that two formulas that differ only in
    // String-vs-interned representation of the *same* variable still collide.
    Some(rewrite_free_vars(formula.clone(), &mapping))
}

/// Rewrite a variable leaf to its canonical `Var(__trust_fvN__<sort>, sort)`.
///
/// `mapping` always contains `name` because the pre-order visitor visits
/// the exact same leaves before the rewrite; the `None` arm is a
/// defensive identity fallback that preserves soundness (it never merges
/// names).
///
/// SOUNDNESS: the canonical NAME embeds the variable's `sort`
/// (`{position}__{sort}`), so two leaves that are structurally identical but
/// differently sorted (`_0 : BitVec(1)` vs `_0 : Int`) can never meet on one
/// name even in an encoding that drops the sort. Position numbering still comes
/// from the by-name `mapping`, so the rename stays a bijection over names;
/// appending the sort can only ever *split* a would-be collision.
fn rename_leaf(name: &str, sort: Sort, mapping: &FxHashMap<&str, usize>) -> Formula {
    let sort_smt: std::borrow::Cow<'static, str> = match &sort {
        Sort::Bool => std::borrow::Cow::Borrowed("Bool"),
        Sort::Int => std::borrow::Cow::Borrowed("Int"),
        Sort::Real => std::borrow::Cow::Borrowed("Real"),
        Sort::RoundingMode => std::borrow::Cow::Borrowed("RoundingMode"),
        Sort::BitVec(1) => std::borrow::Cow::Borrowed("(_ BitVec 1)"),
        Sort::BitVec(8) => std::borrow::Cow::Borrowed("(_ BitVec 8)"),
        Sort::BitVec(16) => std::borrow::Cow::Borrowed("(_ BitVec 16)"),
        Sort::BitVec(32) => std::borrow::Cow::Borrowed("(_ BitVec 32)"),
        Sort::BitVec(64) => std::borrow::Cow::Borrowed("(_ BitVec 64)"),
        Sort::BitVec(128) => std::borrow::Cow::Borrowed("(_ BitVec 128)"),
        Sort::Float { eb: 8, sb: 24 } => std::borrow::Cow::Borrowed("(_ FloatingPoint 8 24)"),
        Sort::Float { eb: 11, sb: 53 } => std::borrow::Cow::Borrowed("(_ FloatingPoint 11 53)"),
        _ => std::borrow::Cow::Owned(sort.to_smtlib()),
    };
    let canonical = match mapping.get(name) {
        Some(&idx) => format!("{FV_CANON_PREFIX}{idx}__{sort_smt}"),
        None => format!("{name}__{sort_smt}"),
    };
    Formula::Var(canonical, sort)
}

#[cfg(test)]
mod tests {
    //! SOUNDNESS CONTRACT under test: two queries hash EQUAL iff they are
    //! alpha-equivalent (identical structure up to one consistent bijective
    //! free-variable rename across every assertion). Each "differ" test guards
    //! a distinct way the canonicalizer could otherwise conflate two queries.

    use super::*;

    /// The hash of the query `assertions` (every formula here serializes).
    fn q(assertions: &[&Formula]) -> String {
        canonical_query_hash(assertions).expect("a test formula serializes")
    }

    /// The hash of the one-assertion query `formula`.
    fn h(formula: &Formula) -> String {
        q(&[formula])
    }

    fn ivar(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    /// What [`canonical_query_hash`] hashes for the one-assertion query
    /// `formula` on the raw (un-canonicalized) fallback path: serde's complete
    /// structural representation of the query.
    fn raw_fallback_hash(formula: &Formula) -> String {
        let query = Formula::And(vec![formula.clone()]);
        crate::digest::stable_sha256_hex(
            serde_json::to_string(&query).expect("Formula serializes").as_bytes(),
        )
    }

    #[test]
    fn hash_is_deterministic_and_separates_distinct_formulas() {
        let f = Formula::Gt(Box::new(ivar("x")), Box::new(Formula::Int(0)));
        assert_eq!(h(&f), h(&f));
        assert_ne!(h(&Formula::Bool(true)), h(&Formula::Bool(false)));
    }

    /// `_0 < _1` in `f` and `_3 < _7` in `g` are one obligation.
    #[test]
    fn alpha_equivalent_formulas_hash_equal() {
        let f1 = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let f2 = Formula::Lt(Box::new(ivar("_3")), Box::new(ivar("_7")));
        assert_eq!(h(&f1), h(&f2));
    }

    /// `_0 < _0` and `_5 < _5` are alpha-equivalent; `_0 < _0` and `_0 < _1`
    /// are not.
    #[test]
    fn repeated_variable_structure_is_preserved() {
        let same_a = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_0")));
        let same_b = Formula::Lt(Box::new(ivar("_5")), Box::new(ivar("_5")));
        assert_eq!(h(&same_a), h(&same_b));
        let distinct = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        assert_ne!(h(&same_a), h(&distinct));
    }

    #[test]
    fn a_differing_constant_or_operator_splits_the_hash() {
        let c0 = Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(0)));
        let c1 = Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(1)));
        assert_ne!(h(&c0), h(&c1));
        let lt = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let gt = Formula::Gt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        assert_ne!(h(&lt), h(&gt));
    }

    /// Swapping two free variables of a query in which nothing else is
    /// asserted IS an alpha-renaming (`_0 < _1` and `_1 < _0`, each the whole
    /// query, ask the same question), so they collide; swapping a variable
    /// with a constant is NOT, so they do not. Under an assertion that
    /// constrains one of the names they are different questions (next test).
    #[test]
    fn variable_swaps_collide_and_variable_constant_swaps_do_not() {
        let ab = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let ba = Formula::Lt(Box::new(ivar("_1")), Box::new(ivar("_0")));
        assert_eq!(h(&ab), h(&ba));
        let var_lt_const = Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(5)));
        let const_lt_var = Formula::Lt(Box::new(Formula::Int(5)), Box::new(ivar("_0")));
        assert_ne!(h(&var_lt_const), h(&const_lt_var));
    }

    /// The renaming is one mapping across every assertion in scope. Under an
    /// assertion that pins `_0`, `_0 < _1` and `_1 < _0` are different queries
    /// and split; the same query with every name renamed consistently,
    /// assertion included, still collides.
    #[test]
    fn a_swap_under_a_constraining_assertion_splits_the_hash() {
        let pin = |name| Formula::Eq(Box::new(ivar(name)), Box::new(Formula::Int(0)));
        let ab = Formula::Lt(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let ba = Formula::Lt(Box::new(ivar("_1")), Box::new(ivar("_0")));
        assert_ne!(q(&[&pin("_0"), &ab]), q(&[&pin("_0"), &ba]));
        assert_eq!(q(&[&pin("_0"), &ab]), q(&[&pin("_1"), &ba]));
        assert_ne!(q(&[&pin("_0"), &ab]), h(&ab), "a query is not its VC formula alone");
    }

    /// `_0 + _1` (two locals) and `_0 + _0` (one local used twice) differ.
    #[test]
    fn distinct_variables_are_never_merged() {
        let two = Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let one = Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_0")));
        assert_ne!(h(&two), h(&one));
        // A source name mimicking the canonical `name__sort` shape changes nothing.
        let two = Formula::Lt(
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
            Box::new(Formula::Var("_1".into(), Sort::Int)),
        );
        let one = Formula::Lt(
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
            Box::new(Formula::Var("_0__Int".into(), Sort::Int)),
        );
        assert_ne!(h(&two), h(&one));
    }

    /// Quantified formulas fail closed to the raw hash, and two
    /// non-equivalent ones still differ.
    #[test]
    fn quantified_formulas_take_the_raw_hash() {
        let quant = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(ivar("_0")),
            )),
        );
        assert!(alpha_canonicalize_free_vars(&quant).is_none());
        assert_eq!(h(&quant), raw_fallback_hash(&quant));
        let other = Formula::Exists(
            vec![("a".into(), Sort::Int)],
            Box::new(Formula::Lt(
                Box::new(Formula::Var("a".into(), Sort::Int)),
                Box::new(ivar("_0")),
            )),
        );
        assert_ne!(h(&quant), h(&other));
    }

    /// A formula already using the reserved prefix fails closed to the raw hash.
    #[test]
    fn a_reserved_prefix_name_takes_the_raw_hash() {
        let collides = Formula::Lt(
            Box::new(Formula::Var(format!("{FV_CANON_PREFIX}0"), Sort::Int)),
            Box::new(ivar("_1")),
        );
        assert!(alpha_canonicalize_free_vars(&collides).is_none());
        assert_eq!(h(&collides), raw_fallback_hash(&collides));
    }

    #[test]
    fn var_and_symvar_in_one_position_collide() {
        let with_var = Formula::Lt(Box::new(ivar("_0")), Box::new(Formula::Int(5)));
        let with_symvar = Formula::Lt(
            Box::new(Formula::SymVar(crate::Symbol::intern("_0"), Sort::Int)),
            Box::new(Formula::Int(5)),
        );
        assert_eq!(h(&with_var), h(&with_symvar));
    }

    /// Predicate ARGUMENTS are canonicalized; the predicate NAME is not.
    #[test]
    fn predicate_arguments_are_canonicalized_and_names_kept() {
        let p_a = Formula::Pred(crate::Symbol::intern("dir_open"), vec![ivar("_0")]);
        let p_b = Formula::Pred(crate::Symbol::intern("dir_open"), vec![ivar("_9")]);
        assert_eq!(h(&p_a), h(&p_b));
        let q = Formula::Pred(crate::Symbol::intern("file_open"), vec![ivar("_0")]);
        assert_ne!(h(&p_a), h(&q));
    }

    /// Every payload channel the SMT-LIB renderer drops still splits the hash:
    /// floating-point formats, uninterpreted result sorts, leaf sorts, BV
    /// widths (top-level and nested), `BvToInt` width and signedness, extract
    /// bounds, and extension kind and amount.
    #[test]
    fn every_dropped_payload_channel_splits_the_hash() {
        assert_ne!(h(&Formula::FpNaN { eb: 8, sb: 24 }), h(&Formula::FpNaN { eb: 11, sb: 53 }));
        let app = |sort| Formula::FnApp { func: "model".to_string(), args: vec![ivar("_0")], sort };
        assert_ne!(h(&app(Sort::Int)), h(&app(Sort::Bool)));

        let sorts = [
            Sort::Bool,
            Sort::Int,
            Sort::BitVec(1),
            Sort::BitVec(8),
            Sort::BitVec(32),
            Sort::Float { eb: 8, sb: 24 },
            Sort::Float { eb: 11, sb: 53 },
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
            Sort::RoundingMode,
        ];
        let hashes: Vec<String> =
            sorts.iter().map(|s| h(&Formula::Var("_0".into(), s.clone()))).collect();
        for i in 0..hashes.len() {
            for j in (i + 1)..hashes.len() {
                assert_ne!(hashes[i], hashes[j], "{:?} vs {:?}", sorts[i], sorts[j]);
            }
        }

        // distinct(a,b,c) is UNSAT over BitVec(1) and SAT over Int, and the two
        // render to identical SMT-LIB text.
        let distinct3 = |sort: Sort| {
            let v = |n: &str| Formula::Var(n.into(), sort.clone());
            Formula::And(vec![
                Formula::Not(Box::new(Formula::Eq(Box::new(v("_0")), Box::new(v("_1"))))),
                Formula::Not(Box::new(Formula::Eq(Box::new(v("_0")), Box::new(v("_2"))))),
                Formula::Not(Box::new(Formula::Eq(Box::new(v("_1")), Box::new(v("_2"))))),
            ])
        };
        assert_eq!(distinct3(Sort::BitVec(1)).to_smtlib(), distinct3(Sort::Int).to_smtlib());
        assert_ne!(h(&distinct3(Sort::BitVec(1))), h(&distinct3(Sort::Int)));

        let bvadd = |w: u32| {
            Formula::BvAdd(
                Box::new(Formula::Var("_0".into(), Sort::BitVec(w))),
                Box::new(Formula::Var("_1".into(), Sort::BitVec(w))),
                w,
            )
        };
        assert_ne!(h(&bvadd(8)), h(&bvadd(16)));
        let nested = |w: u32| {
            Formula::And(vec![
                Formula::Eq(
                    Box::new(bvadd(w)),
                    Box::new(Formula::Var("_2".into(), Sort::BitVec(w))),
                ),
                Formula::Bool(true),
            ])
        };
        assert_ne!(h(&nested(8)), h(&nested(16)));

        let b2i = |w: u32, signed: bool| {
            Formula::Eq(
                Box::new(Formula::BvToInt(
                    Box::new(Formula::Var("_0".into(), Sort::BitVec(w))),
                    w,
                    signed,
                )),
                Box::new(Formula::Int(0)),
            )
        };
        assert_ne!(h(&b2i(8, false)), h(&b2i(16, false)));
        assert_ne!(h(&b2i(8, false)), h(&b2i(8, true)));
        assert_ne!(h(&b2i(16, false)), h(&b2i(8, true)));

        let ext = |high: u32, low: u32| {
            Formula::Eq(
                Box::new(Formula::BvExtract {
                    inner: Box::new(Formula::Var("_0".into(), Sort::BitVec(32))),
                    high,
                    low,
                }),
                Box::new(Formula::Var("_1".into(), Sort::BitVec(high - low + 1))),
            )
        };
        assert_ne!(h(&ext(7, 0)), h(&ext(15, 8)));

        let inner = || Box::new(Formula::Var("_0".into(), Sort::BitVec(8)));
        assert_ne!(h(&Formula::BvZeroExt(inner(), 8)), h(&Formula::BvZeroExt(inner(), 16)));
        assert_ne!(h(&Formula::BvZeroExt(inner(), 8)), h(&Formula::BvSignExt(inner(), 8)));
    }

    /// Folding sorts and widths does not regress the intended merge.
    #[test]
    fn alpha_equivalent_formulas_still_collide_across_sorts() {
        let bv = |a: &str, b: &str| {
            Formula::BvAdd(
                Box::new(Formula::Var(a.into(), Sort::BitVec(8))),
                Box::new(Formula::Var(b.into(), Sort::BitVec(8))),
                8,
            )
        };
        assert_eq!(h(&bv("_0", "_1")), h(&bv("_4", "_9")));
        let eq32 = |a: &str, b: &str| {
            Formula::Eq(
                Box::new(Formula::Var(a.into(), Sort::BitVec(32))),
                Box::new(Formula::Var(b.into(), Sort::BitVec(32))),
            )
        };
        assert_eq!(h(&eq32("_0", "_1")), h(&eq32("_9", "_4")));
        let f32_ = Sort::Float { eb: 8, sb: 24 };
        let fp = |a: &str, b: &str| {
            Formula::FpEq(
                Box::new(Formula::Var(a.into(), f32_.clone())),
                Box::new(Formula::Var(b.into(), f32_.clone())),
            )
        };
        assert_eq!(h(&fp("_0", "_1")), h(&fp("_7", "_3")));
    }

    /// Hashing an already-canonical formula is stable: the second pass bails
    /// on the reserved prefix and hashes the canonical form raw.
    #[test]
    fn canonicalization_is_idempotent_under_the_hash() {
        let f = Formula::Add(Box::new(ivar("_0")), Box::new(ivar("_1")));
        let canon = alpha_canonicalize_free_vars(&f).expect("quantifier-free");
        assert!(alpha_canonicalize_free_vars(&canon).is_none());
        assert_eq!(h(&canon), raw_fallback_hash(&canon));
    }
}
