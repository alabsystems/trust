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
// ever spell an ay builtin.
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
// variable symbol occurrence — free `Var`/`SymVar` leaves AND `Forall`/`Exists`
// BINDERS. A bijective relabeling of variable symbols preserves the formula up
// to alpha-equivalence (binding structure, shadowing and free/bound status are
// all preserved because binder and occurrence are renamed by the same map), and
// satisfiability is invariant under alpha-equivalence. It can therefore neither
// create nor destroy a model: no false PROVE, no false refutation.
//
// Non-variable symbols (`Pred`/`FnApp` names, datatype/constructor/selector
// names) are deliberately NOT renamed — see [`reserved_symbol_handed_to_ay`].
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

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
///   `escaped_reserved_names_are_not_reserved`, which runs ay's own predicate
///   over the escaped form of every reserved name Trust knows of).
/// * It is a valid SMT-LIB simple-symbol prefix, so the text lane renders
///   without needing `|…|` quoting it would not already have needed.
///
/// "Future" is covered belt-and-braces: [`reserved_symbol_handed_to_ay`] still
/// asks ay itself whether any symbol is reserved, so if ay ever reserves a name
/// in this namespace the obligation fails closed to `Unknown` instead of
/// panicking.
pub(crate) const AY_USER_SYMBOL_PREFIX: &str = "__trust_u_";

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

/// Rewrite every VARIABLE symbol in `formula` into Trust's ay namespace.
///
/// Covers all three variable-symbol positions: `Var` names, `SymVar` names and
/// `Forall`/`Exists` BINDER names. `Formula::map` reconstructs quantifier nodes
/// without touching their binding list, so the binders are rewritten explicitly
/// here — renaming an occurrence without its binder would turn a bound variable
/// into a free one and silently change the formula's meaning (an implicitly
/// existential free variable where a universal was intended).
///
/// Everything else — sorts, predicate/function symbols, datatype member names,
/// constants, widths, structure — is carried through verbatim by
/// `Formula::map`.
#[must_use]
pub(crate) fn escape_formula_user_symbols(formula: &Formula) -> Formula {
    formula.clone().map(&mut |node| match node {
        Formula::Var(name, sort) => Formula::Var(escape_user_symbol(&name), sort),
        Formula::SymVar(sym, sort) => {
            Formula::SymVar(Symbol::intern(&escape_user_symbol(sym.as_str())), sort)
        }
        Formula::Forall(bindings, body) => Formula::Forall(escape_bindings(bindings), body),
        Formula::Exists(bindings, body) => Formula::Exists(escape_bindings(bindings), body),
        other => other,
    })
}

/// Rewrite a quantifier's binding list with [`escape_user_symbol`].
fn escape_bindings(bindings: Vec<(Symbol, Sort)>) -> Vec<(Symbol, Sort)> {
    bindings
        .into_iter()
        .map(|(sym, sort)| (Symbol::intern(&escape_user_symbol(sym.as_str())), sort))
        .collect()
}

/// The first symbol in `formula` that ay would REFUSE to declare, if any.
///
/// `formula` must already be [`escape_formula_user_symbols`]-mapped: this is
/// the last gate before the program is handed to ay, and it answers the
/// question "is any symbol in the program ay is about to execute a reserved
/// one?" using ay's OWN predicate, so it tracks ay's table automatically.
///
/// Variable symbols are in Trust's namespace by then and can only trip this if
/// a future ay reserves that namespace. The symbols that CAN still trip it are
/// the ones deliberately left un-namespaced:
///
/// * `Pred` / `FnApp` symbols. These are not variables: `Pred` names come from
///   a closed reviewed vocabulary and a collision means the VC may have MEANT
///   ay's builtin (the `int2bv` class). Silently re-spelling one to an
///   uninterpreted stand-in would drop the builtin's semantics and could
///   manufacture a spurious SAT witness, i.e. a false REFUTATION. Failing
///   closed to `Unknown` is the conservative answer and preserves the existing
///   documented decision.
/// * Datatype sort / constructor / selector names. Renaming these is not a
///   relabeling of one leaf: the name is the identity of the sort, it recurs in
///   by-name back-edges, and ay's `Uninterpreted("T")` <-> `Datatype{name:"T"}`
///   declaration-upgrade path is keyed by it. Until that whole family is mapped
///   consistently, an obligation over a datatype whose Rust-derived member name
///   collides fails closed.
///
/// Returning `Some(name)` is never a proof and never a refutation — the caller
/// declines the obligation as `Unknown`.
#[must_use]
pub(crate) fn reserved_symbol_handed_to_ay(formula: &Formula) -> Option<String> {
    let mut found: Option<String> = None;
    formula.visit(&mut |node| match node {
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

    /// A datatype whose Rust-derived selector name collides is reported, not
    /// silently declared (ay would refuse the `declare-datatype`).
    #[test]
    fn test_reserved_symbol_handed_to_ay_reports_reserved_datatype_member() {
        let sort = Sort::Datatype {
            name: "Config".into(),
            constructors: vec![("Config".into(), vec![("default".into(), Sort::Int)])],
        };
        let formula = Formula::Eq(
            Box::new(Formula::Var("c".into(), sort.clone())),
            Box::new(Formula::Var("d".into(), sort)),
        );
        let escaped = escape_formula_user_symbols(&formula);
        assert_eq!(reserved_symbol_handed_to_ay(&escaped).as_deref(), Some("default"));
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
}
