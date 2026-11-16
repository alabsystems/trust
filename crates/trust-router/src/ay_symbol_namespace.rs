// trust-router/ay_symbol_namespace.rs: the Trust -> ay symbol-namespace map.
//
// Trust: ay REFUSES to declare a symbol whose name is one of its builtin
// theory-operator names (`fp`, `default`, `select`, `store`, `concat`,
// `extract`, `repeat`, `RNE`, `map.get`, …) or that enters its internal
// `__ay_` namespace — see `ay_frontend::is_reserved_symbol`. That refusal is a
// SOUNDNESS gate on ay's side: a user symbol spelled like a builtin is a
// forged-builtin conflation and has produced confirmed wrong-UNSATs, so ay must
// keep rejecting it.
//
// Trust's VC variable names, by contrast, come straight from MIR
// `var_debug_info` — they are raw Rust identifiers. `let fp = …` in any crate
// therefore handed ay a reserved name, and ay's rejection surfaced as a
// `panic!` inside `ay_dpll::api::terms::declare_const`, i.e. a compiler ICE
// (92 of them in one orca-alab workspace build).
//
// The fix is a NAMESPACE, not an allowlist: every user-derived VARIABLE symbol
// is mapped into a Trust-owned prefix before it is handed to ay, so no user
// identifier — present or future, whatever ay adds to its reserved table — can
// ever spell an ay builtin. The datatype family (sort, constructor and selector
// names — Rust type, variant and field names) is mapped the same way, each
// class under its own prefix (TRUST-05): a Rust field named `default` used to
// decline, and one named `__trust_u_kind` used to collide with the namespaced
// local `kind`.
//
// ## Why this seam
//
// This is the Formula -> ay boundary. Upstream (`trust-vcgen`, `trust_verify`,
// `trust-mc`, the interval/wp/ty backends, diagnostics, counterexample
// rendering, the solver cache's alpha-canonical hash) every one of those
// consumers keys off the SOURCE spelling; renaming there would change what the
// user is shown and what every other backend sees, to satisfy one backend's
// namespace policy. Downstream (`ay-bindings`, `ay-dpll`) is ay's own surface,
// where the reserved-name rejection IS the soundness gate — an embedder must
// map its namespace INTO ay's, never weaken ay's. So the mapping belongs
// exactly here, applied by the two ay-facing renderers (`build_program`, the
// native lane, and `problem_smt2`, the text/evidence lane) so both agree
// symbol-for-symbol.
//
// ## Why it is sound
//
// [`escape_formula_user_symbols`] applies ONE injective function to EVERY
// symbol occurrence of every class it owns — variables (free `Var`/`SymVar`
// leaves AND `Forall`/`Exists` BINDERS), datatype sorts, constructors and
// selectors (in every sort position AND every `Ctor`/`Sel`/`IsCtor` term), and
// the uninterpreted `Pred`/`FnApp` symbols that enter the reserved `__trust_`
// prefix. A relabeling of symbols that is injective and applied uniformly to
// declarations and occurrences alike is a renaming of the signature: every
// model of the source formula is a model of the image under the same
// interpretation, read through the renaming, and vice versa. It can therefore
// neither create nor destroy a model: no false PROVE, no false refutation.
// For variables the same argument is alpha-equivalence (binding structure,
// shadowing and free/bound status are preserved because binder and occurrence
// are renamed together).
//
// Injectivity is the whole argument, and it holds ACROSS classes, not merely
// within each one: every class owns its own prefix (`__trust_u_` variables,
// `__trust_d_` datatype sorts, `__trust_c_` constructors, `__trust_s_`
// selectors, `__trust_n_` re-prefixed functions), no prefix is a prefix of
// another, and the only symbols left un-prefixed — `Pred`/`FnApp` names that
// do NOT start with `__trust_` — cannot start with any of them. Two distinct
// source entities therefore never reach ay as one symbol (TRUST-05): before
// this map covered the datatype family, a field literally named
// `__trust_u_kind` collided with the namespaced local `kind`, and a `FnApp`
// named `__trust_u_x` with the namespaced variable `x`.
//
// ## The datatype family (TRUST-04)
//
// SMT-LIB constructors and selectors are GLOBAL function symbols, but Rust
// member names are only unique per TYPE (a constructor) or per VARIANT (a
// field). So the constructor and selector images are QUALIFIED by their
// datatype — two Rust enums may both have a variant `Var` — through a
// length-prefixed pair encoding that is injective for arbitrary strings. The
// per-VARIANT half is not decidable here: a `Formula::Sel` names its datatype
// and field but not its constructor, so the Ty -> Sort lowering
// (`trust_types::datatype_selector_name`) already qualifies each field by its
// constructor, and [`datatype_member_collision`] declines any declaration
// that still lists one member name twice — such a declaration is ambiguous in
// the SOURCE, and no renaming can tell its two members apart.
//
// The datatype-family images are also valid SMT-LIB SIMPLE symbols by
// construction (every other character is `$`-escaped), because the text lane
// renders a datatype declaration's names verbatim (`Sort::to_smtlib`,
// `Sort::datatype_declarations`) while it `|…|`-quotes the same names in
// terms; a Rust def path (`clean_kernel::level::Level`) is not a simple symbol,
// so the two spellings used to disagree.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;
use std::fmt::Write as _;

use ay_bindings::execute_direct::ModelValue;
use trust_types::{Formula, Sort, Symbol};

/// Prefix that maps a user-derived variable symbol into Trust's own namespace.
///
/// Chosen so the image of [`escape_user_symbol`] is disjoint from ay's reserved
/// space by CONSTRUCTION rather than by enumeration:
///
/// * `ay_frontend::is_reserved_symbol` is `starts_with("__ay_") ||
///   RESERVED_OP_NAMES.contains(name) || is_declaration_activated_op_name(name)`.
///   A name starting with `__trust_u_` cannot start with `__ay_`, and no entry
///   of either finite table starts with `__trust_u_` (asserted by
///   `test_escape_user_symbol_reserved_names_are_not_reserved_after_escaping`,
///   which runs ay's own predicate over the escaped form of every reserved name
///   Trust knows of).
/// * It is a valid SMT-LIB simple-symbol prefix, so the text lane renders
///   without needing `|…|` quoting it would not already have needed.
///
/// "Future" is covered belt-and-braces: [`reserved_symbol_handed_to_ay`] still
/// asks ay itself whether any symbol is reserved, so if ay ever reserves a name
/// in this namespace the obligation fails closed to `Unknown` instead of
/// panicking.
pub(crate) const AY_USER_SYMBOL_PREFIX: &str = "__trust_u_";

/// The prefix Trust reserves for every symbol it mints at the ay boundary.
/// Every class prefix below extends it; a `Pred`/`FnApp` name that already
/// starts with it is moved under [`AY_FUNCTION_SYMBOL_PREFIX`] so it cannot
/// land on another class's image.
pub(crate) const AY_TRUST_NAMESPACE: &str = "__trust_";

/// Prefix of a datatype SORT image ([`escape_datatype_sort`]).
pub(crate) const AY_DATATYPE_SORT_PREFIX: &str = "__trust_d_";

/// Prefix of a CONSTRUCTOR image ([`escape_constructor`]); testers reference
/// the constructor, so they share it.
pub(crate) const AY_CONSTRUCTOR_PREFIX: &str = "__trust_c_";

/// Prefix of a SELECTOR image ([`escape_selector`]).
pub(crate) const AY_SELECTOR_PREFIX: &str = "__trust_s_";

/// Prefix of a `Pred`/`FnApp` symbol whose SOURCE spelling already entered the
/// reserved `__trust_` namespace ([`escape_function_symbol`]).
pub(crate) const AY_FUNCTION_SYMBOL_PREFIX: &str = "__trust_n_";

/// Map one user-derived variable symbol into Trust's ay namespace.
///
/// Injective: `x -> PREFIX ++ x` for every `x`, so two distinct source
/// variables can never collapse onto one ay symbol (a merge would be a
/// SOUNDNESS bug — it would equate two independent variables).
#[must_use]
pub(crate) fn escape_user_symbol(name: &str) -> String {
    format!("{AY_USER_SYMBOL_PREFIX}{name}")
}

/// Left inverse of [`escape_user_symbol`]: recover the source spelling of a
/// symbol ay reports back (model/counterexample bindings).
///
/// Strips exactly ONE prefix, so a source name that itself began with the
/// prefix round-trips. A name without the prefix — an ay-internal symbol that
/// appears in a model — is returned unchanged rather than mangled.
#[must_use]
pub(crate) fn unescape_user_symbol(name: &str) -> String {
    name.strip_prefix(AY_USER_SYMBOL_PREFIX).unwrap_or(name).to_string()
}

/// Recover the source spelling of a symbol ay binds in a MODEL: a variable
/// ([`unescape_user_symbol`]) or a nullary `Pred`/`FnApp` constant
/// ([`escape_function_symbol`]'s left inverse).
///
/// A nullary uninterpreted symbol is lowered and declared as an ay constant, so
/// ay's model binds it beside the variables. A variable image starts with
/// `__trust_u_`, a re-prefixed function image with `__trust_n_`, and every
/// other function image lies outside `__trust_`, so stripping whichever ONE of
/// the two prefixes is present decodes each class correctly. Two source
/// entities that share a spelling across classes (a local `y` and a nullary
/// `y()`) are two ay symbols and decode to the same name, exactly as the text
/// lane's `(get-model)` reports them.
#[must_use]
pub(crate) fn unescape_model_symbol(name: &str) -> String {
    match name.strip_prefix(AY_FUNCTION_SYMBOL_PREFIX) {
        Some(function) => function.to_string(),
        None => unescape_user_symbol(name),
    }
}

/// Map a datatype SORT name into Trust's ay namespace: `__trust_d_` followed
/// by the name's [`push_simple`] spelling. Injective (a fixed prefix over an
/// injective spelling), a valid SMT-LIB simple symbol, and never reserved.
#[must_use]
pub(crate) fn escape_datatype_sort(name: &str) -> String {
    let mut out = String::from(AY_DATATYPE_SORT_PREFIX);
    push_simple(&mut out, name);
    out
}

/// Map constructor `ctor` of datatype `datatype` into Trust's ay namespace.
///
/// Qualified by the datatype because SMT-LIB constructors are global: two Rust
/// enums that both declare a variant `Var` must not declare one symbol twice.
#[must_use]
pub(crate) fn escape_constructor(datatype: &str, ctor: &str) -> String {
    member_image(AY_CONSTRUCTOR_PREFIX, datatype, ctor)
}

/// Map selector `field` of datatype `datatype` into Trust's ay namespace.
///
/// Qualified by the datatype for the same reason as [`escape_constructor`].
/// `field` is the selector name the declaration carries, which the Ty -> Sort
/// lowering has already qualified by its constructor
/// (`trust_types::datatype_selector_name`).
#[must_use]
pub(crate) fn escape_selector(datatype: &str, field: &str) -> String {
    member_image(AY_SELECTOR_PREFIX, datatype, field)
}

/// Map an uninterpreted `Pred`/`FnApp` symbol into Trust's ay namespace.
///
/// These keep their SOURCE spelling — a `Pred` comes from a closed reviewed
/// vocabulary, and one spelled like an ay builtin may have MEANT the builtin
/// (the `int2bv` class), which [`reserved_symbol_handed_to_ay`] declines
/// rather than re-spelling. The one exception is a name that already lies in
/// Trust's own `__trust_` namespace: it is moved under `__trust_n_`, so a
/// function named `__trust_u_x` can never become the namespaced variable `x`
/// (a merge that would equate a function with an independent variable).
///
/// Injective: names outside `__trust_` map to themselves, names inside it map
/// to `__trust_n_ ++ name`, and the two images are disjoint because only the
/// second starts with `__trust_`.
#[must_use]
pub(crate) fn escape_function_symbol(name: &str) -> String {
    if name.starts_with(AY_TRUST_NAMESPACE) {
        format!("{AY_FUNCTION_SYMBOL_PREFIX}{name}")
    } else {
        name.to_string()
    }
}

/// `prefix ++ len(D') ++ "_" ++ D' ++ "_" ++ M'`, where `D'`/`M'` are the
/// [`push_simple`] spellings of the datatype and the member.
///
/// The decimal length of `D'` frames it, so the pair decodes uniquely no matter
/// which characters either component contains: that is what makes the map
/// injective on `(datatype, member)` PAIRS, not just on each component.
fn member_image(prefix: &str, datatype: &str, member: &str) -> String {
    let mut datatype_part = String::new();
    push_simple(&mut datatype_part, datatype);
    let mut out = String::from(prefix);
    let _ = write!(out, "{}_{datatype_part}_", datatype_part.len());
    push_simple(&mut out, member);
    out
}

/// Append `name` spelled with SMT-LIB simple-symbol characters only.
///
/// ASCII alphanumerics, `_` and `.` pass through; every other character,
/// including `$` itself, becomes `$<hex code point>$`. Because a bare `$`
/// never survives, each escape is delimited unambiguously and the spelling is
/// injective ([`from_simple`] inverts it).
fn push_simple(out: &mut String, name: &str) {
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '.' {
            out.push(c);
        } else {
            let _ = write!(out, "${:x}$", u32::from(c));
        }
    }
}

/// Inverse of [`push_simple`]; `None` for a string it cannot have produced.
fn from_simple(spelled: &str) -> Option<String> {
    let mut out = String::new();
    let mut chars = spelled.chars();
    while let Some(c) = chars.next() {
        if c == '$' {
            let mut hex = String::new();
            loop {
                match chars.next()? {
                    '$' => break,
                    digit => hex.push(digit),
                }
            }
            out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
        } else {
            out.push(c);
        }
    }
    Some(out)
}

/// Decode a [`member_image`] under `prefix` back to `(datatype, member)`.
fn decode_member_image(prefix: &str, image: &str) -> Option<(String, String)> {
    let rest = image.strip_prefix(prefix)?;
    let (length, rest) = rest.split_once('_')?;
    let length: usize = length.parse().ok()?;
    let datatype = rest.get(..length)?;
    let member = rest.get(length..)?.strip_prefix('_')?;
    Some((from_simple(datatype)?, from_simple(member)?))
}

/// The SOURCE spelling of a datatype sort image, for diagnostics: a decline
/// reason names `clean_kernel::level::Level`, not its ay image. A name that is
/// not a sort image is returned unchanged.
#[must_use]
pub(crate) fn unescape_datatype_sort(image: &str) -> String {
    image
        .strip_prefix(AY_DATATYPE_SORT_PREFIX)
        .and_then(from_simple)
        .unwrap_or_else(|| image.to_string())
}

/// The SOURCE spelling of a constructor ay reports back in a model value.
/// A name that is not a constructor image (an ay-internal one) is returned
/// unchanged rather than mangled.
#[must_use]
pub(crate) fn unescape_constructor(image: &str) -> String {
    decode_member_image(AY_CONSTRUCTOR_PREFIX, image)
        .map_or_else(|| image.to_string(), |(_, ctor)| ctor)
}

/// A model value with every datatype constructor re-spelled in its SOURCE
/// form (see [`unescape_constructor`]), recursively through constructor
/// arguments, arrays and sequences. A witness is read by people and by the
/// refutation machinery, both of which know `Succ`, not its ay image.
#[must_use]
pub(crate) fn unescape_model_value(value: &ModelValue) -> ModelValue {
    match value {
        ModelValue::Datatype { constructor, args } => ModelValue::Datatype {
            constructor: unescape_constructor(constructor),
            args: args.iter().map(unescape_model_value).collect(),
        },
        ModelValue::Array { default, stores } => ModelValue::Array {
            default: Box::new(unescape_model_value(default)),
            stores: stores
                .iter()
                .map(|(index, element)| {
                    (unescape_model_value(index), unescape_model_value(element))
                })
                .collect(),
        },
        ModelValue::Seq(items) => ModelValue::Seq(items.iter().map(unescape_model_value).collect()),
        other => other.clone(),
    }
}

/// Map every symbol a sort introduces — the datatype name, its constructors
/// and its selectors, recursively through fields and array sorts — into
/// Trust's ay namespace. A by-name reference maps to the same sort image as
/// its definition, so back-edges and ay's `Uninterpreted("T")` <->
/// `Datatype{name:"T"}` declaration-upgrade key stay on one name.
#[cfg_attr(not(test), allow(dead_code))]
#[must_use]
pub(crate) fn escape_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Array(index, element) => {
            Sort::Array(Box::new(escape_sort(*index)), Box::new(escape_sort(*element)))
        }
        Sort::Datatype { name, constructors } => {
            let constructors = constructors
                .into_iter()
                .map(|(ctor, fields)| {
                    let fields = fields
                        .into_iter()
                        .map(|(field, field_sort)| {
                            (escape_selector(&name, &field), escape_sort(field_sort))
                        })
                        .collect();
                    (escape_constructor(&name, &ctor), fields)
                })
                .collect();
            Sort::Datatype { name: escape_datatype_sort(&name), constructors }
        }
        other => other,
    }
}

#[must_use]
fn escape_sort_ref(sort: &Sort) -> Sort {
    match sort {
        Sort::Int => Sort::Int,
        Sort::Bool => Sort::Bool,
        Sort::Real => Sort::Real,
        Sort::BitVec(w) => Sort::BitVec(*w),
        Sort::Float { eb, sb } => Sort::Float { eb: *eb, sb: *sb },
        Sort::RoundingMode => Sort::RoundingMode,
        Sort::Array(index, element) => {
            Sort::Array(Box::new(escape_sort_ref(index)), Box::new(escape_sort_ref(element)))
        }
        Sort::Datatype { name, constructors } => {
            let constructors = constructors
                .iter()
                .map(|(ctor, fields)| {
                    let fields = fields
                        .iter()
                        .map(|(field, field_sort)| {
                            (escape_selector(name, field), escape_sort_ref(field_sort))
                        })
                        .collect();
                    (escape_constructor(name, ctor), fields)
                })
                .collect();
            Sort::Datatype { name: escape_datatype_sort(name), constructors }
        }
        other => escape_sort(other.clone()),
    }
}

/// Rewrite every symbol in `formula` into Trust's ay namespace.
///
/// * VARIABLES — `Var` names, `SymVar` names and `Forall`/`Exists` BINDER
///   names — through [`escape_user_symbol`]. `Formula::map` reconstructs
///   quantifier nodes without touching their binding list, so the binders are
///   rewritten explicitly here: renaming an occurrence without its binder
///   would turn a bound variable into a free one and silently change the
///   formula's meaning (an implicitly existential free variable where a
///   universal was intended).
/// * THE DATATYPE FAMILY — every sort position ([`escape_sort`]) and every
///   `Ctor`/`Sel`/`IsCtor` term, each member qualified by the datatype it
///   belongs to (a `Ctor`'s is its result sort's name).
/// * `Pred`/`FnApp` symbols — through [`escape_function_symbol`].
///
/// Built in a single borrowed-to-owned pass over `formula` rather than
/// `formula.clone().map(..)`, halving AST/string allocations per query.
#[must_use]
pub(crate) fn escape_formula_user_symbols(formula: &Formula) -> Formula {
    let rec = escape_formula_user_symbols;
    match formula {
        Formula::Bool(v) => Formula::Bool(*v),
        Formula::Int(n) => Formula::Int(*n),
        Formula::UInt(n) => Formula::UInt(*n),
        Formula::Rat(lit) => Formula::Rat(lit.clone()),
        Formula::BitVec { value, width } => Formula::BitVec { value: *value, width: *width },
        Formula::Var(name, sort) => {
            Formula::Var(escape_user_symbol(name), escape_sort_ref(sort))
        }
        Formula::SymVar(sym, sort) => Formula::SymVar(
            Symbol::intern(&escape_user_symbol(sym.as_str())),
            escape_sort_ref(sort),
        ),
        Formula::Not(a) => Formula::Not(Box::new(rec(a))),
        Formula::Neg(a) => Formula::Neg(Box::new(rec(a))),
        Formula::And(terms) => Formula::And(terms.iter().map(rec).collect()),
        Formula::Or(terms) => Formula::Or(terms.iter().map(rec).collect()),
        Formula::Implies(a, b) => Formula::Implies(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Eq(a, b) => Formula::Eq(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Lt(a, b) => Formula::Lt(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Le(a, b) => Formula::Le(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Gt(a, b) => Formula::Gt(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Ge(a, b) => Formula::Ge(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Add(a, b) => Formula::Add(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Sub(a, b) => Formula::Sub(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Mul(a, b) => Formula::Mul(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Div(a, b) => Formula::Div(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Rem(a, b) => Formula::Rem(Box::new(rec(a)), Box::new(rec(b))),
        Formula::BvNot(a, w) => Formula::BvNot(Box::new(rec(a)), *w),
        Formula::BvToInt(a, w, s) => Formula::BvToInt(Box::new(rec(a)), *w, *s),
        Formula::IntToBv(a, w) => Formula::IntToBv(Box::new(rec(a)), *w),
        Formula::BvZeroExt(a, bits) => Formula::BvZeroExt(Box::new(rec(a)), *bits),
        Formula::BvSignExt(a, bits) => Formula::BvSignExt(Box::new(rec(a)), *bits),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: Box::new(rec(inner)), high: *high, low: *low }
        }
        Formula::BvConcat(a, b) => Formula::BvConcat(Box::new(rec(a)), Box::new(rec(b))),
        Formula::BvAdd(a, b, w) => Formula::BvAdd(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvSub(a, b, w) => Formula::BvSub(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvMul(a, b, w) => Formula::BvMul(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvUDiv(a, b, w) => Formula::BvUDiv(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvSDiv(a, b, w) => Formula::BvSDiv(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvURem(a, b, w) => Formula::BvURem(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvSRem(a, b, w) => Formula::BvSRem(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvAnd(a, b, w) => Formula::BvAnd(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvOr(a, b, w) => Formula::BvOr(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvXor(a, b, w) => Formula::BvXor(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvShl(a, b, w) => Formula::BvShl(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvLShr(a, b, w) => Formula::BvLShr(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvAShr(a, b, w) => Formula::BvAShr(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvULt(a, b, w) => Formula::BvULt(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvULe(a, b, w) => Formula::BvULe(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvSLt(a, b, w) => Formula::BvSLt(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::BvSLe(a, b, w) => Formula::BvSLe(Box::new(rec(a)), Box::new(rec(b)), *w),
        Formula::Ite(a, b, c) => {
            Formula::Ite(Box::new(rec(a)), Box::new(rec(b)), Box::new(rec(c)))
        }
        Formula::Select(a, b) => Formula::Select(Box::new(rec(a)), Box::new(rec(b))),
        Formula::Store(a, b, c) => {
            Formula::Store(Box::new(rec(a)), Box::new(rec(b)), Box::new(rec(c)))
        }
        Formula::ConstArray { index_sort, elem_sort, value } => Formula::ConstArray {
            index_sort: index_sort.clone(),
            elem_sort: elem_sort.clone(),
            value: Box::new(rec(value)),
        },
        Formula::FpConst { bits, eb, sb } => Formula::FpConst { bits: *bits, eb: *eb, sb: *sb },
        Formula::FpNaN { eb, sb } => Formula::FpNaN { eb: *eb, sb: *sb },
        Formula::FpInf { neg, eb, sb } => Formula::FpInf { neg: *neg, eb: *eb, sb: *sb },
        Formula::FpZero { neg, eb, sb } => Formula::FpZero { neg: *neg, eb: *eb, sb: *sb },
        Formula::FpRoundingMode(rm) => Formula::FpRoundingMode(*rm),
        Formula::FpNeg(a) => Formula::FpNeg(Box::new(rec(a))),
        Formula::FpAbs(a) => Formula::FpAbs(Box::new(rec(a))),
        Formula::FpIsNaN(a) => Formula::FpIsNaN(Box::new(rec(a))),
        Formula::FpIsInfinite(a) => Formula::FpIsInfinite(Box::new(rec(a))),
        Formula::FpIsZero(a) => Formula::FpIsZero(Box::new(rec(a))),
        Formula::FpIsNormal(a) => Formula::FpIsNormal(Box::new(rec(a))),
        Formula::FpIsSubnormal(a) => Formula::FpIsSubnormal(Box::new(rec(a))),
        Formula::FpIsNegative(a) => Formula::FpIsNegative(Box::new(rec(a))),
        Formula::FpIsPositive(a) => Formula::FpIsPositive(Box::new(rec(a))),
        Formula::FpFromBits { bits, eb, sb } => {
            Formula::FpFromBits { bits: Box::new(rec(bits)), eb: *eb, sb: *sb }
        }
        Formula::FpToIeeeBv(a) => Formula::FpToIeeeBv(Box::new(rec(a))),
        Formula::FpToSbv { rm, value, width, eb, sb } => Formula::FpToSbv {
            rm: Box::new(rec(rm)),
            value: Box::new(rec(value)),
            width: *width,
            eb: *eb,
            sb: *sb,
        },
        Formula::FpToUbv { rm, value, width, eb, sb } => Formula::FpToUbv {
            rm: Box::new(rec(rm)),
            value: Box::new(rec(value)),
            width: *width,
            eb: *eb,
            sb: *sb,
        },
        Formula::FpFromSbv { rm, value, eb, sb } => {
            Formula::FpFromSbv { rm: Box::new(rec(rm)), value: Box::new(rec(value)), eb: *eb, sb: *sb }
        }
        Formula::FpFromUbv { rm, value, eb, sb } => {
            Formula::FpFromUbv { rm: Box::new(rec(rm)), value: Box::new(rec(value)), eb: *eb, sb: *sb }
        }
        Formula::FpConvert { rm, value, eb, sb } => {
            Formula::FpConvert { rm: Box::new(rec(rm)), value: Box::new(rec(value)), eb: *eb, sb: *sb }
        }
        Formula::FpRem(a, b) => Formula::FpRem(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpMin(a, b) => Formula::FpMin(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpMax(a, b) => Formula::FpMax(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpEq(a, b) => Formula::FpEq(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpLt(a, b) => Formula::FpLt(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpLe(a, b) => Formula::FpLe(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpGt(a, b) => Formula::FpGt(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpGe(a, b) => Formula::FpGe(Box::new(rec(a)), Box::new(rec(b))),
        Formula::FpSqrt(rm, a) => Formula::FpSqrt(Box::new(rec(rm)), Box::new(rec(a))),
        Formula::FpAdd(rm, a, b) => {
            Formula::FpAdd(Box::new(rec(rm)), Box::new(rec(a)), Box::new(rec(b)))
        }
        Formula::FpSub(rm, a, b) => {
            Formula::FpSub(Box::new(rec(rm)), Box::new(rec(a)), Box::new(rec(b)))
        }
        Formula::FpMul(rm, a, b) => {
            Formula::FpMul(Box::new(rec(rm)), Box::new(rec(a)), Box::new(rec(b)))
        }
        Formula::FpDiv(rm, a, b) => {
            Formula::FpDiv(Box::new(rec(rm)), Box::new(rec(a)), Box::new(rec(b)))
        }
        Formula::FpFma(rm, a, b, c) => Formula::FpFma(
            Box::new(rec(rm)),
            Box::new(rec(a)),
            Box::new(rec(b)),
            Box::new(rec(c)),
        ),
        Formula::Forall(bindings, body) => {
            Formula::Forall(escape_bindings_ref(bindings), Box::new(rec(body)))
        }
        Formula::Exists(bindings, body) => {
            Formula::Exists(escape_bindings_ref(bindings), Box::new(rec(body)))
        }
        Formula::Pred(name, args) => Formula::Pred(
            Symbol::intern(&escape_function_symbol(name.as_str())),
            args.iter().map(rec).collect(),
        ),
        Formula::FnApp { func, args, sort } => Formula::FnApp {
            func: escape_function_symbol(func),
            args: args.iter().map(rec).collect(),
            sort: escape_sort_ref(sort),
        },
        Formula::Ctor { ctor, args, sort } => {
            // A `Ctor` whose sort is not a datatype is ill-formed and is declined
            // before any program is built (`check_datatype_terms`); there is no
            // datatype to qualify it by, so it keeps its spelling.
            let ctor = match sort {
                Sort::Datatype { name, .. } => escape_constructor(name, ctor),
                _ => ctor.clone(),
            };
            Formula::Ctor { ctor, args: args.iter().map(rec).collect(), sort: escape_sort_ref(sort) }
        }
        Formula::Sel { datatype, field, field_sort, arg } => Formula::Sel {
            field: escape_selector(datatype, field),
            datatype: escape_datatype_sort(datatype),
            field_sort: escape_sort_ref(field_sort),
            arg: Box::new(rec(arg)),
        },
        Formula::IsCtor { datatype, ctor, arg } => Formula::IsCtor {
            ctor: escape_constructor(datatype, ctor),
            datatype: escape_datatype_sort(datatype),
            arg: Box::new(rec(arg)),
        },
        #[allow(unreachable_patterns)]
        other => other.clone().map_children(&mut |child| escape_formula_user_symbols(&child)),
    }
}

/// Rewrite a quantifier's binding list: names with [`escape_user_symbol`],
/// sorts with [`escape_sort`].
fn escape_bindings_ref(bindings: &[(Symbol, Sort)]) -> Vec<(Symbol, Sort)> {
    bindings
        .iter()
        .map(|(sym, sort)| {
            (Symbol::intern(&escape_user_symbol(sym.as_str())), escape_sort_ref(sort))
        })
        .collect()
}

/// A datatype declaration in `formula` that lists one member name twice, if
/// any — the precondition the namespace cannot supply.
///
/// [`escape_formula_user_symbols`] is injective on `(datatype, member)` pairs,
/// so it keeps every two DIFFERENTLY-named members apart; it cannot separate
/// two members that already share one name inside one declaration, because a
/// `Sel` names only `(datatype, field)` and so cannot say which of them it
/// selects. Such a declaration is ambiguous in the source: declaring it hands
/// ay one function symbol for two fields (possibly at two sorts). Measured on
/// the pinned ay, the declaration is accepted and the name resolves to ONE of
/// the fields, so reads of the others are refused as sort mismatches; a
/// consumer without that check would conflate them — `l.Max.0 != l.IMax.0`
/// would read `t != t`, a false PROVE. The caller DECLINES up front instead,
/// with the ambiguity named (sound: neither a proof nor a refutation).
///
/// Checked over every full definition reachable from any sort position,
/// including definitions nested in field sorts.
#[must_use]
pub(crate) fn datatype_member_collision(formula: &Formula) -> Option<String> {
    let mut found: Option<String> = None;
    trust_types::smt_logic::visit_sort_positions(formula, &mut |sort| {
        if found.is_none() {
            found = sort_member_collision(sort);
        }
    });
    found
}

/// [`datatype_member_collision`] for one sort, recursively.
fn sort_member_collision(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Array(index, element) => {
            sort_member_collision(index).or_else(|| sort_member_collision(element))
        }
        Sort::Datatype { name, constructors } => {
            let mut ctors = BTreeSet::new();
            let mut selectors = BTreeSet::new();
            for (ctor, fields) in constructors {
                if !ctors.insert(ctor.as_str()) {
                    return Some(format!(
                        "datatype `{name}` declares constructor `{ctor}` twice, so the two \
                         constructors cannot be told apart"
                    ));
                }
                for (field, _) in fields {
                    if !selectors.insert(field.as_str()) {
                        return Some(format!(
                            "datatype `{name}` declares selector `{field}` more than once \
                             (again in constructor `{ctor}`); SMT-LIB selectors are one function \
                             per datatype, so a selection by that name cannot say which field it \
                             reads"
                        ));
                    }
                }
            }
            constructors
                .iter()
                .flat_map(|(_, fields)| fields.iter())
                .find_map(|(_, field_sort)| sort_member_collision(field_sort))
        }
        _ => None,
    }
}

/// The first symbol in `formula` that ay would REFUSE to declare, if any.
///
/// `formula` must already be [`escape_formula_user_symbols`]-mapped: this is
/// the last gate before the program is handed to ay, and it answers the
/// question "is any symbol in the program ay is about to execute a reserved
/// one?" using ay's OWN predicate, so it tracks ay's table automatically.
///
/// Variable and datatype-family symbols are in Trust's namespace by then and
/// can only trip this if a future ay reserves that namespace. The symbols
/// that CAN still trip it are the ones deliberately left un-namespaced: the
/// `Pred` / `FnApp` symbols outside `__trust_`. These are not variables:
/// `Pred` names come from a closed reviewed vocabulary and a collision means
/// the VC may have MEANT ay's builtin (the `int2bv` class). Silently
/// re-spelling one to an uninterpreted stand-in would drop the builtin's
/// semantics and could manufacture a spurious SAT witness, i.e. a false
/// REFUTATION. Failing closed to `Unknown` is the conservative answer and
/// preserves the existing documented decision.
///
/// Returning `Some(name)` is never a proof and never a refutation — the caller
/// declines the obligation as `Unknown`.
#[must_use]
pub(crate) fn reserved_symbol_handed_to_ay(formula: &Formula) -> Option<String> {
    let mut found: Option<String> = None;
    let _ = trust_types::all_formula_nodes(formula, &mut |node| {
        match node {
            Formula::Var(name, sort) => {
                note_symbol(name, &mut found);
                note_sort_symbols(sort, &mut found);
            }
            Formula::SymVar(sym, sort) => {
                note_symbol(sym.as_str(), &mut found);
                note_sort_symbols(sort, &mut found);
            }
            Formula::Forall(bindings, _) | Formula::Exists(bindings, _) => {
                for (sym, sort) in bindings {
                    note_symbol(sym.as_str(), &mut found);
                    note_sort_symbols(sort, &mut found);
                }
            }
            Formula::Pred(name, _) => note_symbol(name.as_str(), &mut found),
            Formula::FnApp { func, sort, .. } => {
                note_symbol(func, &mut found);
                note_sort_symbols(sort, &mut found);
            }
            Formula::Ctor { ctor, sort, .. } => {
                note_symbol(ctor, &mut found);
                note_sort_symbols(sort, &mut found);
            }
            Formula::Sel { datatype, field, field_sort, .. } => {
                note_symbol(datatype, &mut found);
                note_symbol(field, &mut found);
                note_sort_symbols(field_sort, &mut found);
            }
            Formula::IsCtor { datatype, ctor, .. } => {
                note_symbol(datatype, &mut found);
                note_symbol(ctor, &mut found);
            }
            _ => {}
        }
        found.is_none()
    });
    found
}

/// Record `name` as the reported symbol if ay reserves it and nothing has been
/// reported yet (first hit in visit order wins, for a deterministic message).
fn note_symbol(name: &str, found: &mut Option<String>) {
    if found.is_none() && ay::is_reserved_symbol(name) {
        *found = Some(name.to_string());
    }
}

/// Report every symbol a sort would introduce into ay's symbol table: the
/// datatype sort name plus each constructor and selector name, recursively
/// through array index/element sorts and nested field sorts.
fn note_sort_symbols(sort: &Sort, found: &mut Option<String>) {
    match sort {
        Sort::Array(index, element) => {
            note_sort_symbols(index, found);
            note_sort_symbols(element, found);
        }
        Sort::Datatype { name, constructors } => {
            note_symbol(name, found);
            for (ctor, fields) in constructors {
                note_symbol(ctor, found);
                for (field, field_sort) in fields {
                    note_symbol(field, found);
                    note_sort_symbols(field_sort, found);
                }
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests_for_ay_symbol_namespace {
    use trust_types::Sort;

    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    /// Every reserved ay name Trust can plausibly receive from a Rust
    /// identifier must leave the reserved space once escaped — asked of ay's
    /// OWN predicate, so the property is checked against ay's table, not a
    /// copy of it. Includes the `__ay_` internal namespace and one entry from
    /// every reserved family (`is_reserved_symbol` = `__ay_` prefix, the
    /// theory-operator table, and the declaration-activated collection
    /// predicates).
    #[test]
    fn test_escape_user_symbol_reserved_names_are_not_reserved_after_escaping() {
        let reserved = [
            // FP theory — the name that ICEd the orca-alab workspace build.
            "fp",
            "fp.abs",
            "RNE",
            "roundTowardZero",
            // Arrays.
            "select",
            "store",
            "default",
            "const-array",
            "as-array",
            // Bit-vectors.
            "concat",
            "extract",
            "repeat",
            "int2bv",
            "bv2nat",
            "zero_extend",
            "bvadd",
            // Collections / sequences / strings / regex.
            "set.union",
            "map.get",
            "multiset.count",
            "seq.len",
            "str.len",
            "re.all",
            "char.to_int",
            "set.empty",
            // Declaration-activated collection predicates.
            "set.subset",
            "map.subset",
            "multiset.subset",
            "map.dom",
            // ay's internal namespace.
            "__ay_",
            "__ay_dt_depth_List",
        ];
        for name in reserved {
            assert!(ay::is_reserved_symbol(name), "expected `{name}` to be reserved in ay");
            let escaped = escape_user_symbol(name);
            assert!(
                !ay::is_reserved_symbol(&escaped),
                "escaped `{name}` -> `{escaped}` is still reserved"
            );
            assert_eq!(unescape_user_symbol(&escaped), name, "escape must round-trip");
        }
    }

    /// The map must be injective: two distinct source names may never collapse
    /// onto one ay symbol. Includes a source name that already carries the
    /// prefix (the only shape that could alias).
    #[test]
    fn test_escape_user_symbol_distinct_names_stay_distinct() {
        let names = ["fp", "x", "__trust_u_fp", "self.0", "_1"];
        for (i, a) in names.iter().enumerate() {
            for b in &names[i + 1..] {
                assert_ne!(escape_user_symbol(a), escape_user_symbol(b), "{a} vs {b}");
            }
            assert_eq!(unescape_user_symbol(&escape_user_symbol(a)), *a);
        }
    }

    /// Free variables are rewritten in place, sorts untouched.
    #[test]
    fn test_escape_formula_user_symbols_free_var_is_namespaced() {
        let formula = Formula::Gt(Box::new(int_var("fp")), Box::new(Formula::Int(3)));
        let escaped = escape_formula_user_symbols(&formula);
        assert_eq!(
            escaped,
            Formula::Gt(Box::new(int_var("__trust_u_fp")), Box::new(Formula::Int(3)))
        );
        assert!(reserved_symbol_handed_to_ay(&escaped).is_none());
    }

    /// A quantifier BINDER is renamed together with its bound occurrences.
    /// Renaming only the occurrence would free the variable and turn a
    /// universal claim into an existential one.
    #[test]
    fn test_escape_formula_user_symbols_binder_and_occurrence_rename_together() {
        let formula = Formula::Forall(
            vec![(Symbol::intern("fp"), Sort::Int)],
            Box::new(Formula::Ge(Box::new(int_var("fp")), Box::new(Formula::Int(0)))),
        );
        let escaped = escape_formula_user_symbols(&formula);
        let Formula::Forall(bindings, body) = &escaped else {
            panic!("expected a Forall, got {escaped:?}");
        };
        assert_eq!(bindings[0].0.as_str(), "__trust_u_fp");
        assert_eq!(
            **body,
            Formula::Ge(Box::new(int_var("__trust_u_fp")), Box::new(Formula::Int(0)))
        );
        // The renamed body has no free variables: the binder still binds it.
        assert!(escaped.free_variables().is_empty(), "renaming freed a bound variable");
    }

    /// Shadowing survives: an inner binder and an outer free variable that
    /// share a spelling keep sharing it, so scoping is unchanged.
    #[test]
    fn test_escape_formula_user_symbols_preserves_shadowing() {
        let inner = Formula::Forall(
            vec![(Symbol::intern("fp"), Sort::Int)],
            Box::new(Formula::Ge(Box::new(int_var("fp")), Box::new(Formula::Int(0)))),
        );
        let formula = Formula::And(vec![
            inner,
            Formula::Lt(Box::new(int_var("fp")), Box::new(Formula::Int(9))),
        ]);
        let escaped = escape_formula_user_symbols(&formula);
        let free: Vec<String> = escaped.free_variables().into_iter().collect();
        assert_eq!(free, vec!["__trust_u_fp".to_string()]);
    }

    /// Non-variable symbols are NOT renamed — and are exactly what the
    /// fail-closed gate reports.
    #[test]
    fn test_reserved_symbol_handed_to_ay_reports_reserved_pred_symbol() {
        let formula = Formula::Pred(Symbol::intern("int2bv"), vec![int_var("x")]);
        let escaped = escape_formula_user_symbols(&formula);
        assert_eq!(reserved_symbol_handed_to_ay(&escaped).as_deref(), Some("int2bv"));
    }

    /// TRUST-05: a datatype whose Rust-derived member names spell ay builtins
    /// (a datatype `fp`, a constructor `concat`, a selector `default`) is
    /// namespaced like a variable is, so nothing in it is reserved any more
    /// and the obligation reaches the solver instead of declining.
    #[test]
    fn test_reserved_symbol_handed_to_ay_accepts_namespaced_builtin_named_datatype_members() {
        let sort = Sort::Datatype {
            name: "fp".into(),
            constructors: vec![("concat".into(), vec![("default".into(), Sort::Int)])],
        };
        let formula = Formula::Eq(
            Box::new(Formula::Var("c".into(), sort.clone())),
            Box::new(Formula::Ctor {
                ctor: "concat".into(),
                args: vec![Formula::Sel {
                    datatype: "fp".into(),
                    field: "default".into(),
                    field_sort: Sort::Int,
                    arg: Box::new(Formula::Var("d".into(), sort.clone())),
                }],
                sort,
            }),
        );
        let escaped = escape_formula_user_symbols(&formula);
        assert_eq!(reserved_symbol_handed_to_ay(&escaped), None, "{escaped:?}");
    }

    /// The whole point: a variable named like an ay builtin is NOT reported —
    /// it is namespaced away, so the obligation still reaches the solver.
    #[test]
    fn test_reserved_symbol_handed_to_ay_accepts_namespaced_builtin_named_variable() {
        for name in ["fp", "default", "select", "store", "concat", "extract", "repeat", "RNE"] {
            let formula = Formula::Gt(Box::new(int_var(name)), Box::new(Formula::Int(0)));
            let escaped = escape_formula_user_symbols(&formula);
            assert_eq!(
                reserved_symbol_handed_to_ay(&escaped),
                None,
                "variable `{name}` should be namespaced, not declined"
            );
        }
    }

    // ── TRUST-04 / TRUST-05: the whole symbol map ──────────────────────────

    /// Which class minted an image, and from what source identity.
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Minted {
        Variable(String),
        Function(String),
        Constructor(String, String),
        Selector(String, String),
    }

    /// Every string of length <= 3 over an alphabet chosen to attack the
    /// encoding — the frame separator `_`, the escape delimiter `$`, a digit
    /// (the frame's length prefix), a letter, `:` (the escaped path separator)
    /// and `.` (the constructor/field separator) — plus whole spellings that
    /// imitate another class's image.
    fn adversarial_names() -> Vec<String> {
        let alphabet = ['_', '$', '1', 'a', ':', '.'];
        let mut names = vec![String::new()];
        let mut frontier = vec![String::new()];
        for _ in 0..3 {
            let mut next = Vec::new();
            for stem in &frontier {
                for c in alphabet {
                    next.push(format!("{stem}{c}"));
                }
            }
            names.extend(next.iter().cloned());
            frontier = next;
        }
        for imitation in [
            "__trust_",
            "__trust_u_x",
            "__trust_n___trust_u_x",
            "__trust_d_a",
            "__trust_c_1_a_b",
            "__trust_s_1_a_b",
            "1_a_b",
            "a_b",
            "$3a$",
            "Level",
            "Succ.0",
            "clean_kernel::level::Level",
        ] {
            names.push(imitation.to_string());
        }
        names
    }

    /// TRUST-05 property: the map is injective ACROSS every class that shares
    /// ay's function namespace — variables, uninterpreted functions,
    /// constructors and selectors (the last two keyed by their datatype) — so
    /// no two distinct source entities can ever be handed to ay as one symbol.
    /// Checked exhaustively over [`adversarial_names`] (≈ 2 × 72k pairs).
    #[test]
    fn test_escape_is_injective_across_every_symbol_class() {
        let names = adversarial_names();
        let mut seen: std::collections::HashMap<String, Minted> = std::collections::HashMap::new();
        let mut mint = |image: String, source: Minted| {
            if let Some(previous) = seen.insert(image.clone(), source.clone()) {
                assert_eq!(previous, source, "`{image}` is the image of two source symbols");
            }
        };
        for name in &names {
            mint(escape_user_symbol(name), Minted::Variable(name.clone()));
            mint(escape_function_symbol(name), Minted::Function(name.clone()));
        }
        for datatype in &names {
            for member in &names {
                mint(
                    escape_constructor(datatype, member),
                    Minted::Constructor(datatype.clone(), member.clone()),
                );
                mint(
                    escape_selector(datatype, member),
                    Minted::Selector(datatype.clone(), member.clone()),
                );
            }
        }
        // Sort names live in their own SMT-LIB namespace; they must still be
        // injective among themselves.
        let sorts: std::collections::BTreeSet<String> =
            names.iter().map(|name| escape_datatype_sort(name)).collect();
        assert_eq!(sorts.len(), names.iter().collect::<std::collections::BTreeSet<_>>().len());
    }

    /// Every datatype-family image is a valid SMT-LIB SIMPLE symbol, so the
    /// text lane's verbatim declaration spelling and its `|…|`-quoting term
    /// spelling agree; and none is reserved by ay, whatever the source name.
    #[test]
    fn test_datatype_family_images_are_simple_symbols_and_never_reserved() {
        for datatype in
            ["Level", "clean_kernel::level::Level", "fp", "Foo<(u8, i32)>", "Größe", "$"]
        {
            for member in ["Succ", "Succ.0", "default", "select", "__trust_u_kind", "0", "a b"] {
                for image in [
                    escape_datatype_sort(datatype),
                    escape_constructor(datatype, member),
                    escape_selector(datatype, member),
                ] {
                    assert_eq!(
                        trust_types::escape_smtlib_symbol(&image),
                        image,
                        "`{image}` would be quoted in a term but not in its declaration"
                    );
                    assert!(!ay::is_reserved_symbol(&image), "`{image}` is reserved in ay");
                }
            }
        }
    }

    /// A witness names constructors in their SOURCE spelling, whatever
    /// characters the datatype or constructor carries; a name that is not a
    /// constructor image is left alone.
    #[test]
    fn test_constructor_images_decode_to_their_source_spelling() {
        for (datatype, ctor) in
            [("Level", "Succ"), ("clean_kernel::level::Level", "IMax"), ("a_1_b", "c_d"), ("", "")]
        {
            assert_eq!(unescape_constructor(&escape_constructor(datatype, ctor)), ctor);
            assert_eq!(unescape_datatype_sort(&escape_datatype_sort(datatype)), datatype);
        }
        assert_eq!(unescape_datatype_sort("Level"), "Level");
        assert_eq!(unescape_constructor("succ"), "succ");
        assert_eq!(unescape_constructor("__trust_c_9_short"), "__trust_c_9_short");

        let witness = ModelValue::Datatype {
            constructor: escape_constructor("Level", "Succ"),
            args: vec![ModelValue::Datatype {
                constructor: escape_constructor("Level", "Zero"),
                args: vec![],
            }],
        };
        assert_eq!(unescape_model_value(&witness).to_string(), "(Succ Zero)");
    }

    fn level_ty() -> trust_types::Ty {
        use trust_types::Ty;
        let level_ref = || Ty::Datatype { name: "Level".into(), variants: vec![] };
        Ty::Datatype {
            name: "Level".into(),
            variants: vec![
                ("Zero".into(), vec![]),
                ("Succ".into(), vec![("0".into(), level_ref())]),
                ("Max".into(), vec![("0".into(), level_ref()), ("1".into(), level_ref())]),
                ("Param".into(), vec![("0".into(), Ty::Int { width: 64, signed: false })]),
            ],
        }
    }

    /// Every datatype position is renamed by the SAME map: after escaping, the
    /// formula is still a well-formed datatype query — each `Ctor`/`Sel`/
    /// `IsCtor` names a member its (renamed) definition declares, and a
    /// by-name back-edge names the same sort as its definition.
    #[test]
    fn test_escape_renames_every_datatype_position_consistently() {
        use trust_types::SortFromTy;
        use trust_types::ay_bridge::{DatatypeDefs, check_datatype_terms};

        let level = Sort::from_ty(&level_ty());
        let Sort::Datatype { constructors, .. } = &level else { panic!("datatype") };
        let (succ_field, succ_sort) = constructors[1].1[0].clone();
        let l = Formula::Var("l".into(), level.clone());
        let formula = Formula::Forall(
            vec![(Symbol::intern("m"), level.clone())],
            Box::new(Formula::And(vec![
                Formula::IsCtor {
                    datatype: "Level".into(),
                    ctor: "Succ".into(),
                    arg: Box::new(l.clone()),
                },
                Formula::Eq(
                    Box::new(Formula::Sel {
                        datatype: "Level".into(),
                        field: succ_field,
                        field_sort: succ_sort,
                        arg: Box::new(l),
                    }),
                    Box::new(Formula::Ctor {
                        ctor: "Zero".into(),
                        args: vec![],
                        sort: level.clone(),
                    }),
                ),
                Formula::Eq(
                    Box::new(Formula::Var("m".into(), level.clone())),
                    Box::new(Formula::Var("m".into(), level)),
                ),
            ])),
        );
        let escaped = escape_formula_user_symbols(&formula);
        let defs = DatatypeDefs::collect(&escaped).expect("one definition per renamed name");
        check_datatype_terms(&escaped, &defs).expect("renamed terms still match the definition");
        assert!(defs.get("Level").is_none(), "no position kept the source sort name");
        assert!(defs.get(&escape_datatype_sort("Level")).is_some());
        assert_eq!(datatype_member_collision(&escaped), None);
    }

    /// The precondition the namespace cannot supply: a declaration that lists
    /// one member name twice is ambiguous in the SOURCE, and is reported.
    #[test]
    fn test_datatype_member_collision_reports_a_member_declared_twice() {
        let level_ref = Sort::Datatype { name: "Level".into(), constructors: vec![] };
        let raw_level = Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("Succ".into(), vec![("0".into(), level_ref.clone())]),
                ("Param".into(), vec![("0".into(), Sort::BitVec(64))]),
            ],
        };
        let formula = Formula::Eq(
            Box::new(Formula::Var("l".into(), raw_level.clone())),
            Box::new(Formula::Var("m".into(), raw_level)),
        );
        let reason = datatype_member_collision(&formula).expect("selector `0` is declared twice");
        assert!(reason.contains("selector `0`"), "{reason}");

        // A duplicated constructor, nested inside an array element sort.
        let twice = Sort::Datatype {
            name: "T".into(),
            constructors: vec![("A".into(), vec![]), ("A".into(), vec![])],
        };
        let nested = Formula::Eq(
            Box::new(Formula::Var(
                "a".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(twice.clone())),
            )),
            Box::new(Formula::Var("b".into(), Sort::Array(Box::new(Sort::Int), Box::new(twice)))),
        );
        assert!(datatype_member_collision(&nested).is_some_and(|r| r.contains("constructor `A`")));

        // The Ty -> Sort lowering never produces one.
        use trust_types::SortFromTy;
        let level = Sort::from_ty(&level_ty());
        let lowered = Formula::Eq(
            Box::new(Formula::Var("l".into(), level.clone())),
            Box::new(Formula::Var("m".into(), level)),
        );
        assert_eq!(datatype_member_collision(&lowered), None);
    }

    /// A model binds variables AND nullary function constants; each decodes to
    /// its source spelling, over every name in [`adversarial_names`] — a
    /// function named like a namespaced variable included.
    #[test]
    fn test_model_symbols_decode_to_their_source_spelling() {
        for name in adversarial_names() {
            assert_eq!(unescape_model_symbol(&escape_user_symbol(&name)), name);
            assert_eq!(unescape_model_symbol(&escape_function_symbol(&name)), name);
        }
        assert_eq!(unescape_model_symbol("__trust_n___trust_u_x"), "__trust_u_x");
        assert_eq!(unescape_model_symbol("__ay_internal"), "__ay_internal");
    }

    #[test]
    fn test_escape_formula_user_symbols_single_pass_matches_clone_map_oracle() {
        use trust_types::{RoundingMode, SortFromTy};

        let level = Sort::from_ty(&level_ty());
        let sample = Formula::And(vec![
            Formula::Forall(
                vec![(Symbol::intern("q"), level.clone())],
                Box::new(Formula::Implies(
                    Box::new(Formula::IsCtor {
                        datatype: "Level".into(),
                        ctor: "Zero".into(),
                        arg: Box::new(Formula::SymVar(Symbol::intern("q"), level.clone())),
                    }),
                    Box::new(Formula::Eq(
                        Box::new(Formula::FnApp {
                            func: "__trust_u_fn".into(),
                            args: vec![Formula::Var("fp".into(), Sort::Int)],
                            sort: level.clone(),
                        }),
                        Box::new(Formula::Ctor {
                            ctor: "Zero".into(),
                            args: vec![],
                            sort: level,
                        }),
                    )),
                )),
            ),
            Formula::Pred(
                Symbol::intern("user_pred"),
                vec![
                    Formula::Select(
                        Box::new(Formula::Store(
                            Box::new(Formula::ConstArray {
                                index_sort: Sort::Int,
                                elem_sort: Sort::BitVec(32),
                                value: Box::new(Formula::BitVec { value: 1, width: 32 }),
                            }),
                            Box::new(Formula::Int(0)),
                            Box::new(Formula::BvAdd(
                                Box::new(Formula::Var("bv".into(), Sort::BitVec(32))),
                                Box::new(Formula::BitVec { value: 2, width: 32 }),
                                32,
                            )),
                        )),
                        Box::new(Formula::Int(0)),
                    ),
                    Formula::FpFma(
                        Box::new(Formula::FpRoundingMode(RoundingMode::RNE)),
                        Box::new(Formula::FpAdd(
                            Box::new(Formula::FpRoundingMode(RoundingMode::RNE)),
                            Box::new(Formula::Var("fa".into(), Sort::Float { eb: 8, sb: 24 })),
                            Box::new(Formula::FpConst { bits: 0x3f800000, eb: 8, sb: 24 }),
                        )),
                        Box::new(Formula::FpZero { neg: false, eb: 8, sb: 24 }),
                        Box::new(Formula::FpInf { neg: true, eb: 8, sb: 24 }),
                    ),
                ],
            ),
        ]);

        let oracle = sample.clone().map(&mut |node| match node {
            Formula::Var(name, sort) => Formula::Var(escape_user_symbol(&name), escape_sort(sort)),
            Formula::SymVar(sym, sort) => Formula::SymVar(
                Symbol::intern(&escape_user_symbol(sym.as_str())),
                escape_sort(sort),
            ),
            Formula::Forall(bindings, body) => {
                Formula::Forall(escape_bindings_ref(&bindings), body)
            }
            Formula::Exists(bindings, body) => {
                Formula::Exists(escape_bindings_ref(&bindings), body)
            }
            Formula::Pred(name, args) => {
                Formula::Pred(Symbol::intern(&escape_function_symbol(name.as_str())), args)
            }
            Formula::FnApp { func, args, sort } => {
                Formula::FnApp { func: escape_function_symbol(&func), args, sort: escape_sort(sort) }
            }
            Formula::Ctor { ctor, args, sort } => {
                let ctor = match &sort {
                    Sort::Datatype { name, .. } => escape_constructor(name, &ctor),
                    _ => ctor,
                };
                Formula::Ctor { ctor, args, sort: escape_sort(sort) }
            }
            Formula::Sel { datatype, field, field_sort, arg } => Formula::Sel {
                field: escape_selector(&datatype, &field),
                datatype: escape_datatype_sort(&datatype),
                field_sort: escape_sort(field_sort),
                arg,
            },
            Formula::IsCtor { datatype, ctor, arg } => Formula::IsCtor {
                ctor: escape_constructor(&datatype, &ctor),
                datatype: escape_datatype_sort(&datatype),
                arg,
            },
            other => other,
        });

        assert_eq!(escape_formula_user_symbols(&sample), oracle);
    }
}
