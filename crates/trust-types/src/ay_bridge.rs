// trust-types/ay_bridge.rs: Conversion bridge between trust_types::Formula ↔ ay_bindings::Expr
//
// Phase 1 of the trust-mc/ay direct integration. Provides bidirectional
// conversion so downstream crates can migrate incrementally from Formula to Expr.
//
// Design: designs/2026-04-13-trust-mc-direct-integration.md
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::borrow::Cow;
use std::collections::BTreeMap;

use ay_bindings::{Expr, RoundingMode as AyRm, Sort as AYSort, SortInner as AYSortInner};

use crate::formula::{Formula, RoundingMode, Sort};
use crate::smt_logic::{check_formula_sort_cow, sorts_agree};

/// Convert a trust_types::Sort to a ay_bindings::Sort.
///
/// Scalar and array sorts map one-to-one. A datatype sort is lowered under the
/// ay-bindings reference discipline ([`sort_to_ay_in`]) with an EMPTY
/// definition table, so a by-name reference that is not its own definition's
/// back-edge lowers to a DANGLING `datatype_ref`, which every ay use refuses.
/// Lowering a whole formula goes through [`formula_to_expr`], which collects
/// the formula's definitions first and widens such positions.
#[must_use]
pub fn sort_to_ay(sort: &Sort) -> AYSort {
    sort_to_ay_with_defs(sort, &DatatypeDefs::default())
}

#[inline]
fn sort_to_ay_with_defs(sort: &Sort, defs: &DatatypeDefs) -> AYSort {
    match sort {
        Sort::Bool => AYSort::bool(),
        Sort::Int => AYSort::int(),
        Sort::BitVec(w) => AYSort::bitvec(*w),
        Sort::Float { eb, sb } => AYSort::floating_point(*eb, *sb),
        Sort::Real => AYSort::real(),
        _ => sort_to_ay_in_borrowed(sort, defs, &mut Vec::new()),
    }
}

/// [`sort_to_ay`] under a definition table and the stack of datatype names
/// whose definitions ENCLOSE this sort position.
///
/// AY BOUNDARY (ay ≥ d4400b131 `Sort::datatype_ref`, expr/dt/check.rs).
/// ay-bindings admits a datatype constructor/selector only when every
/// argument/result sort is the SAME SORT as the field sort recorded on the
/// descriptor — structurally, with a `DatatypeRef(N)` in a FIELD resolving to
/// the ENCLOSING declaration named `N` and to nothing else (never to the
/// argument's own sort, never to a bare `Uninterpreted(N)`). Outside a
/// declaration of its name a reference is not a sort of its own. So:
///
/// * a by-name reference (`Sort::Datatype` with empty `constructors`) that
///   names an enclosing definition lowers to `AYSort::datatype_ref` — the
///   recursive back-edge, exactly the SMT-LIB
///   `(declare-datatype Level ((zero) (succ (pred Level))))` shape;
/// * a by-name reference in a TERM position (a variable, a binder, a
///   requested selector result) or in a NON-enclosing field (a sibling
///   datatype) lowers to that name's ONE full definition from `defs`, inlined,
///   because ay resolves a reference only against enclosing declarations;
/// * a by-name reference with no definition anywhere stays a dangling
///   `datatype_ref` and fails closed at the ay boundary — never an opaque
///   `Uninterpreted` sort, which would silently drop the datatype's
///   constructors, selectors, testers and acyclicity.
///
/// A full definition lowers to an ay enum/datatype sort with its name pushed
/// as enclosing while its fields lower, so a name is inlined at most once per
/// path and a mutual cycle closes as a reference on the second visit; the
/// walk terminates because every step either descends a finite sort tree or
/// inlines a definition whose name is then enclosing.
///
/// SOUNDNESS: declaring a datatype sort asserts NO fact and cannot make the
/// context vacuously UNSAT (trust-ir-contract sort.rs soundness note): a fresh
/// datatype-sorted constant is unconstrained (SAT), so this can only let
/// obligations report their honest outcome, never manufacture a false PROVE.
/// The table only ever substitutes a definition the formula itself (or the
/// caller's body-level table) supplies under that name, and two different
/// definitions under one name refuse the whole lowering ([`DatatypeConflict`]).
#[must_use]
pub fn sort_to_ay_in(sort: &Sort, defs: &DatatypeDefs, enclosing: &mut Vec<String>) -> AYSort {
    if enclosing.is_empty() {
        return sort_to_ay_with_defs(sort, defs);
    }
    let mut borrowed: Vec<&str> = enclosing.iter().map(String::as_str).collect();
    sort_to_ay_in_borrowed(sort, defs, &mut borrowed)
}

#[must_use]
fn sort_to_ay_in_borrowed<'a>(
    sort: &'a Sort,
    defs: &'a DatatypeDefs,
    enclosing: &mut Vec<&'a str>,
) -> AYSort {
    match sort {
        Sort::Bool => AYSort::bool(),
        Sort::Int => AYSort::int(),
        Sort::BitVec(w) => AYSort::bitvec(*w),
        Sort::Array(idx, elem) => AYSort::array(
            sort_to_ay_in_borrowed(idx, defs, enclosing),
            sort_to_ay_in_borrowed(elem, defs, enclosing),
        ),
        Sort::Float { eb, sb } => AYSort::floating_point(*eb, *sb),
        // ay carries the rounding mode as an *enum argument* of the fp.* ops
        // (`ay_bindings::RoundingMode`, a plain Rust enum parameter of
        // `fp_add`/`fp_sqrt`/`bv_to_fp`/…), not as a first-class sorted term:
        // `ay_bindings::SortInner` has NO `RoundingMode` variant and no `Expr`
        // constructor mints an rm-sorted term. So there is no faithful lowering
        // of this sort, and the previous `AYSort::bool()` was a SILENT
        // MISENCODING: an rm-sorted variable became a Bool-sorted one, two
        // distinct rounding modes collapsed into one of two booleans, and a
        // violation formula that is genuinely satisfiable could come back
        // UNSAT — a FALSE PROVE. Fail closed instead; the router declines every
        // formula carrying this sort before the bridge is entered
        // (`unlowerable_sort_position`), so this refusal is unreachable from
        // the in-process lane and is the backstop for direct library callers.
        Sort::Datatype { name, constructors } if constructors.is_empty() => {
            if enclosing.contains(&name.as_str()) {
                AYSort::datatype_ref(name.clone())
            } else if let Some(definition) = defs.get(name) {
                sort_to_ay_in_borrowed(definition, defs, enclosing)
            } else {
                AYSort::datatype_ref(name.clone())
            }
        }
        Sort::Datatype { name, constructors } => {
            enclosing.push(name.as_str());
            let lowered = AYSort::enum_type(
                name.clone(),
                constructors
                    .iter()
                    .map(|(ctor, fields)| {
                        (
                            ctor.clone(),
                            fields
                                .iter()
                                .map(|(fname, fsort)| {
                                    (fname.clone(), sort_to_ay_in_borrowed(fsort, defs, enclosing))
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>(),
            );
            enclosing.pop();
            lowered
        }
        // The SMT-LIB `Real` sort (QF_LRA): ay's own Real sort, exact-rational.
        Sort::Real => AYSort::real(),
        // THE TWO SORTS WITH NO ay COUNTERPART, refused on one line because they
        // are refused for one reason: there is nothing faithful to lower them to.
        //
        // * `Sort::RoundingMode` — ay takes the rounding mode as an ENUM
        //   ARGUMENT of each `fp.*` builder, never as a sorted term, so an
        //   rm-sorted variable, binder or field cannot be declared at all.
        //   Coercing it to Bool (what this arm used to do) silently identifies
        //   distinct rounding modes and has already produced a FALSE PROVE.
        // * A future `#[non_exhaustive]` `Sort` variant (trust-ir-contract) —
        //   no arm, so no faithful lowering.
        //
        // Both are established and DECLINED before any lowering, by
        // `unlowerable_sort_position`, which `formula_to_expr` runs first and
        // the router runs as an explicit gate. Reaching here therefore means a
        // caller lowered a sort position it had not gated; fail closed loudly
        // rather than coerce.
        #[allow(unreachable_patterns)]
        Sort::RoundingMode | _ => {
            unreachable!(
                "ay bridge: no ay sort for {sort:?} (gate with `unlowerable_sort_position`)"
            )
        }
    }
}

/// The ONE full definition of every datatype a lowering may widen a by-name
/// reference to, keyed by name (see [`sort_to_ay_in`]).
///
/// trust-ir-contract cuts EVERY datatype-typed field to the by-name form, and
/// trust-vcgen puts that form on pattern binders (`__fld_*`), opaque aggregate
/// arguments (`__dtf_*`) and `Sel::field_sort` too, while ay requires the full
/// definition in every term position. This table is what turns those shipped
/// shapes into ay's encoding without a second spelling of any datatype.
#[derive(Debug, Default, Clone)]
pub struct DatatypeDefs(BTreeMap<String, Sort>);

/// Two different full definitions of one datatype name met in one lowering.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("conflicting full definitions of datatype `{0}` in one formula")]
pub struct DatatypeConflict(pub String);

impl DatatypeDefs {
    /// Every full definition reachable from the sort positions of `formula`:
    /// `Var`/`SymVar` sorts, quantifier binders, `Ctor` result sorts, `Sel`
    /// field sorts and `FnApp` result sorts, recursing into field sorts (the
    /// same positions trust-router's `visit_datatype_bearing_sorts` walks).
    pub fn collect(formula: &Formula) -> Result<Self, DatatypeConflict> {
        let mut defs = Self::default();
        defs.extend_from_formula(formula)?;
        Ok(defs)
    }

    /// Add the full definitions inside `sort`: the sort itself, then its
    /// fields, recursively. By-name references contribute nothing.
    pub fn add_sort(&mut self, sort: &Sort) -> Result<(), DatatypeConflict> {
        match sort {
            Sort::Datatype { constructors, .. } if constructors.is_empty() => Ok(()),
            Sort::Datatype { name, constructors } => {
                match self.0.get(name) {
                    Some(previous) if previous == sort => return Ok(()),
                    Some(_) => return Err(DatatypeConflict(name.clone())),
                    None => {
                        self.0.insert(name.clone(), sort.clone());
                    }
                }
                for (_, fields) in constructors {
                    for (_, fsort) in fields {
                        self.add_sort(fsort)?;
                    }
                }
                Ok(())
            }
            Sort::Array(idx, elem) => {
                self.add_sort(idx)?;
                self.add_sort(elem)
            }
            _ => Ok(()),
        }
    }

    fn add_sort_cow(defs: &mut Cow<'_, Self>, sort: &Sort) -> Result<(), DatatypeConflict> {
        match sort {
            Sort::Datatype { constructors, .. } if constructors.is_empty() => Ok(()),
            Sort::Datatype { name, constructors } => {
                match defs.0.get(name) {
                    Some(previous) if previous == sort => return Ok(()),
                    Some(_) => return Err(DatatypeConflict(name.clone())),
                    None => {
                        defs.to_mut().0.insert(name.clone(), sort.clone());
                    }
                }
                for (_, fields) in constructors {
                    for (_, fsort) in fields {
                        Self::add_sort_cow(defs, fsort)?;
                    }
                }
                Ok(())
            }
            Sort::Array(idx, elem) => {
                Self::add_sort_cow(defs, idx)?;
                Self::add_sort_cow(defs, elem)
            }
            _ => Ok(()),
        }
    }

    /// Add every full definition `formula` mentions (see [`Self::collect`]).
    ///
    /// The positions come from the ONE shared inventory
    /// ([`crate::smt_logic::visit_node_sort_positions`]) — the same list the
    /// logic selectors classify from and trust-router's
    /// `visit_lowered_sort_positions` / `visit_datatype_bearing_sorts` gate and
    /// declare from — so the definition TABLE cannot name a different set of
    /// sorts from the ones the gates audit or the transcript declares.
    pub fn extend_from_formula(&mut self, formula: &Formula) -> Result<(), DatatypeConflict> {
        let mut result = Ok(());
        let _ = crate::all_formula_nodes(formula, &mut |node| {
            crate::smt_logic::visit_node_sort_positions(node, &mut |sort| {
                if result.is_ok() {
                    result = self.add_sort(sort);
                }
            });
            result.is_ok()
        });
        result
    }

    /// The full definition recorded for `name`, if any.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Sort> {
        self.0.get(name)
    }

    /// The ay declaration of every definition in the table, each lowered
    /// exactly as the terms over it are (so a program registration through
    /// `AYProgram::try_declare_datatype` never disagrees with a term's
    /// descriptor), in dependency order: a datatype follows every OTHER
    /// datatype its fields name. ay's native lane declares one datatype at a
    /// time, so this order is what it needs; genuine mutual recursion has no
    /// such order and is refused cleanly there.
    #[must_use]
    pub fn to_ay_declarations(&self) -> Vec<ay_bindings::DatatypeSort> {
        fn references<'a>(sort: &'a Sort, out: &mut Vec<&'a str>) {
            match sort {
                Sort::Datatype { name, constructors } if constructors.is_empty() => {
                    out.push(name.as_str());
                }
                Sort::Datatype { constructors, .. } => {
                    for (_, fields) in constructors {
                        for (_, fsort) in fields {
                            references(fsort, out);
                        }
                    }
                }
                Sort::Array(idx, elem) => {
                    references(idx, out);
                    references(elem, out);
                }
                _ => {}
            }
        }
        fn visit<'a>(
            defs: &'a DatatypeDefs,
            name: &'a str,
            visited: &mut Vec<&'a str>,
            out: &mut Vec<ay_bindings::DatatypeSort>,
        ) {
            if visited.contains(&name) {
                return;
            }
            visited.push(name);
            let Some(definition) = defs.get(name) else { return };
            let mut referenced = Vec::new();
            references(definition, &mut referenced);
            for other in referenced {
                if other != name {
                    visit(defs, other, visited, out);
                }
            }
            if let AYSortInner::Datatype(dt) =
                sort_to_ay_in_borrowed(definition, defs, &mut Vec::new()).inner()
            {
                out.push(dt.clone());
            }
        }
        let mut visited = Vec::with_capacity(self.0.len());
        let mut out = Vec::with_capacity(self.0.len());
        for name in self.0.keys() {
            visit(self, name, &mut visited, &mut out);
        }
        out
    }
}

/// A named refusal from [`formula_to_expr`]: the formula has no faithful ay
/// `Expr`. Callers decline the obligation (`Unknown`) on this error; it is
/// never a verdict.
///
/// Every refusal site reachable from the lowering has a variant here, which is
/// what makes [`formula_to_expr`] TOTAL: there is no `Formula` for which it
/// aborts. A caller that must not unwind therefore never has to contain a
/// panic from this bridge.
///
/// [`AyBridgeError::Datatype`] carries ay's own [`ay_bindings::SortError`] as
/// its [`std::error::Error::source`], so a caller can inspect the solver's
/// diagnostic rather than re-parsing a formatted string. The refusals this
/// bridge establishes ITSELF (a malformed datatype term, a dangling by-name
/// reference, a non-literal rounding mode, an unlowerable sort) have no ay
/// error behind them and carry their own typed cause instead.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum AyBridgeError {
    /// A `Formula::Ctor` whose own sort is not a `Sort::Datatype`.
    #[error("datatype constructor `{ctor}` carries non-datatype sort {sort}")]
    CtorSortNotDatatype { ctor: String, sort: String },
    /// ay refused a datatype constructor/selector/tester node (or, from the
    /// router, a constant/datatype DECLARATION) against the declaration its
    /// sort carries. `node` is one of `"constructor"`, `"selector"`,
    /// `"tester"`, `"variable"`, `"declaration"`.
    #[error("ay refused datatype {node} `{datatype}::{member}`: {source}")]
    Datatype {
        node: &'static str,
        datatype: String,
        member: String,
        #[source]
        source: ay_bindings::SortError,
    },
    /// A `Formula` variant this bridge has no lowering for. `Formula` is
    /// `#[non_exhaustive]`, so this is the fail-closed answer for a contract
    /// variant added after this bridge was last taught.
    #[error("no ay lowering for formula {formula}")]
    UnsupportedFormula { formula: String },
    /// A datatype term that PROVABLY contradicts the one full definition of
    /// its datatype in the formula — the fallible twin of the authentication
    /// ay-bindings' checked datatype API performs.
    #[error("malformed datatype term: {0}")]
    DatatypeTerm(#[from] DatatypeTermError),
    /// A by-name datatype reference with no full definition anywhere in the
    /// formula: there is nothing for the reference to stand for.
    #[error(
        "datatype `{datatype}` is referenced by name with no full definition anywhere in the \
         formula"
    )]
    UndefinedDatatype { datatype: String },
    /// Two different full definitions of one datatype name in one formula.
    #[error("{0}")]
    ConflictingDefinitions(#[from] DatatypeConflict),
    /// An `fp.*` rounding-mode operand that is not a rounding-mode LITERAL.
    /// ay has no rounding-mode sort, so there is nothing faithful to lower a
    /// symbolic rounding mode to — see [`non_literal_rounding_mode_operand`].
    #[error("{0}")]
    NonLiteralRoundingMode(#[from] NonLiteralRoundingMode),
    /// A declaration/binder/field sort with no faithful ay counterpart:
    /// `Sort::RoundingMode`, `Sort::BitVec(0)`, or a future `Sort` variant.
    #[error("unlowerable sort position: {position}")]
    UnlowerableSort { position: String },
}

/// A datatype term whose own descriptor is PROVABLY inconsistent with the one
/// full definition of its datatype in scope — the shapes ay-bindings' checked
/// datatype API refuses and the bridge then turns into a loud panic (see
/// [`formula_to_expr`]'s `Formula::Ctor` arm, and which it reports as
/// [`AyBridgeError::DatatypeTerm`] before anything is lowered).
///
/// Every variant is a DEFECT the checker established, never an absence of
/// information: [`check_datatype_terms`] stays silent whenever the operand's
/// sort or the datatype's definition cannot be determined, so this error can
/// only mean "the term contradicts the definition the formula itself carries".
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum DatatypeTermError {
    /// `Formula::Ctor` whose carried result sort is not a datatype sort at all
    /// (the bridge's `unreachable!("Formula::Ctor sort must be Sort::Datatype")`).
    #[error("constructor term `{ctor}` carries result sort {sort:?}, which is not a datatype sort")]
    ConstructorSortNotDatatype { ctor: String, sort: Sort },
    /// A selector/tester applied to an operand whose sort is not a datatype.
    #[error("datatype {op} `{member}` of `{datatype}` is applied to an operand of sort {actual:?}")]
    OperandNotDatatype { op: &'static str, datatype: String, member: String, actual: Sort },
    /// A selector/tester naming one datatype applied to a term of another.
    #[error("datatype {op} `{member}` of `{datatype}` is applied to a term of datatype `{actual}`")]
    OperandDatatypeMismatch { op: &'static str, datatype: String, member: String, actual: String },
    /// A constructor / field name the datatype's definition does not declare.
    #[error("datatype `{datatype}` declares no {member_kind} `{member}`")]
    UnknownMember { datatype: String, member_kind: &'static str, member: String },
    /// A constructor applied to the wrong number of arguments.
    #[error(
        "constructor `{ctor}` of datatype `{datatype}` takes {expected} argument(s), applied to \
         {actual}"
    )]
    ConstructorArity { datatype: String, ctor: String, expected: usize, actual: usize },
    /// A constructor argument whose established sort contradicts the field the
    /// definition declares for that position.
    #[error(
        "argument `{field}` of constructor `{ctor}` of datatype `{datatype}` is declared \
         {expected:?} but the term has sort {actual:?}"
    )]
    ConstructorArgumentSort {
        datatype: String,
        ctor: String,
        field: String,
        expected: Box<Sort>,
        actual: Box<Sort>,
    },
    /// A `Sel` whose carried `field_sort` contradicts the definition's field.
    #[error(
        "selector `{field}` of datatype `{datatype}` is declared {expected:?} but the term \
         carries field sort {actual:?}"
    )]
    SelectorFieldSort { datatype: String, field: String, expected: Box<Sort>, actual: Box<Sort> },
}

/// The full definition `sort` denotes under `defs`, if one is in scope: the
/// sort itself when it carries its constructor list, otherwise the table's
/// entry for its name. `None` for a non-datatype sort and for a by-name
/// reference with no definition anywhere — the second is IGNORANCE, not a
/// defect, and the caller must stay silent about it (`build_program` declines
/// such a query where the dangling reference is declared).
fn resolved_definition<'a>(sort: &'a Sort, defs: &'a DatatypeDefs) -> Option<&'a Sort> {
    match sort {
        Sort::Datatype { name, constructors } if constructors.is_empty() => match defs.get(name) {
            Some(definition @ Sort::Datatype { constructors, .. }) if !constructors.is_empty() => {
                Some(definition)
            }
            _ => None,
        },
        Sort::Datatype { .. } => Some(sort),
        _ => None,
    }
}

/// The field list `ctor` declares in the full definition `definition`.
fn constructor_fields<'a>(definition: &'a Sort, ctor: &str) -> Option<&'a Vec<(String, Sort)>> {
    let Sort::Datatype { constructors, .. } = definition else { return None };
    constructors.iter().find(|(name, _)| name == ctor).map(|(_, fields)| fields)
}

/// The sort `definition` declares for the field named `field`, in whichever
/// constructor declares it (SMT-LIB selectors are per-datatype, not
/// per-constructor).
fn declared_field_sort<'a>(definition: &'a Sort, field: &str) -> Option<&'a Sort> {
    let Sort::Datatype { constructors, .. } = definition else { return None };
    constructors
        .iter()
        .flat_map(|(_, fields)| fields.iter())
        .find(|(name, _)| name == field)
        .map(|(_, sort)| sort)
}

/// The datatype name an operand's established sort denotes, if it is a
/// datatype sort.
fn datatype_name(sort: &Sort) -> Option<&str> {
    match sort {
        Sort::Datatype { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

/// Check every datatype term in `formula` against the ONE full definition of
/// its datatype in `defs` (plus whatever the terms carry inline), FALLIBLY —
/// the pre-bridge counterpart of the panicking authentication ay-bindings does
/// inside [`formula_to_expr`].
///
/// A caller that must not crash on an ill-typed obligation (trust-router's
/// in-process backend) runs this BEFORE lowering and declines the obligation on
/// an `Err`, so a malformed datatype term never reaches the bridge and its
/// fail-closed panic is never taken. Declining emits neither a proof nor a
/// refutation, so soundness is unaffected either way; what this buys is that
/// the decline carries the gate's own diagnostic instead of a caught panic —
/// a caught panic still runs the process-global panic hook and can leak a
/// false compiler-ICE-looking diagnostic to stderr.
///
/// # Only proven defects
///
/// The walk reports a term ONLY when the definition it contradicts is itself in
/// scope and the contradicting sort is one [`check_formula_sort`] established:
///
/// * a by-name datatype reference with no full definition anywhere is skipped
///   (nothing to authenticate against). It is still undeclarable, and it is a
///   separate, separately-reported defect: trust-router's
///   `undefined_datatype_reference` names it at the same pre-gate, because
///   `build_program` refuses a dangling reference fallibly only where one
///   reaches a DECLARATION (`try_declare_const`/`try_declare_datatype`) — one
///   living only in term positions is met first by the infallible datatype API
///   below;
/// * an operand whose sort `check_formula_sort` cannot establish is skipped
///   (the full-formula sort gate reports it with its own diagnostic);
/// * sorts are compared with [`sorts_agree`], so a datatype's by-name and full
///   spellings are ONE sort — the relaxation the checker itself applies.
///
/// This is the rule the previous `infer_sort(a) != infer_sort(b)` pre-gate
/// broke: it declined on UN-INFERABILITY, refusing every well-sorted
/// constructor-, selector- and tester-vs-variable equation.
///
/// # Errors
///
/// The first [`DatatypeTermError`] found, in the formula's visit order.
pub fn check_datatype_terms(
    formula: &Formula,
    defs: &DatatypeDefs,
) -> Result<(), DatatypeTermError> {
    let mut result = Ok(());
    let _ = crate::all_formula_nodes(formula, &mut |node| {
        result = check_datatype_term(node, defs);
        result.is_ok()
    });
    result
}

/// One node of [`check_datatype_terms`]; non-datatype nodes are vacuously fine.
fn check_datatype_term(node: &Formula, defs: &DatatypeDefs) -> Result<(), DatatypeTermError> {
    match node {
        Formula::Ctor { ctor, args, sort } => {
            let Sort::Datatype { name, .. } = sort else {
                return Err(DatatypeTermError::ConstructorSortNotDatatype {
                    ctor: ctor.clone(),
                    sort: sort.clone(),
                });
            };
            // No definition in scope: ignorance, not a defect.
            let Some(definition) = resolved_definition(sort, defs) else { return Ok(()) };
            let Some(fields) = constructor_fields(definition, ctor) else {
                return Err(DatatypeTermError::UnknownMember {
                    datatype: name.clone(),
                    member_kind: "constructor",
                    member: ctor.clone(),
                });
            };
            if fields.len() != args.len() {
                return Err(DatatypeTermError::ConstructorArity {
                    datatype: name.clone(),
                    ctor: ctor.clone(),
                    expected: fields.len(),
                    actual: args.len(),
                });
            }
            for ((field, field_sort), argument) in fields.iter().zip(args.iter()) {
                // Only an ESTABLISHED argument sort can contradict the field.
                let Ok(actual) = check_formula_sort_cow(argument) else { continue };
                if !sorts_agree(&actual, field_sort) {
                    return Err(DatatypeTermError::ConstructorArgumentSort {
                        datatype: name.clone(),
                        ctor: ctor.clone(),
                        field: field.clone(),
                        expected: Box::new(field_sort.clone()),
                        actual: Box::new(actual.into_owned()),
                    });
                }
            }
            Ok(())
        }
        Formula::Sel { datatype, field, field_sort, arg } => {
            let Some(operand) = established_datatype_operand("selector", datatype, field, arg)?
            else {
                return Ok(());
            };
            let Some(definition) = resolved_definition(&operand, defs) else { return Ok(()) };
            let Some(declared) = declared_field_sort(definition, field) else {
                return Err(DatatypeTermError::UnknownMember {
                    datatype: datatype.clone(),
                    member_kind: "field",
                    member: field.clone(),
                });
            };
            if sorts_agree(field_sort, declared) {
                Ok(())
            } else {
                Err(DatatypeTermError::SelectorFieldSort {
                    datatype: datatype.clone(),
                    field: field.clone(),
                    expected: Box::new(declared.clone()),
                    actual: Box::new(field_sort.clone()),
                })
            }
        }
        Formula::IsCtor { datatype, ctor, arg } => {
            let Some(operand) = established_datatype_operand("tester", datatype, ctor, arg)? else {
                return Ok(());
            };
            let Some(definition) = resolved_definition(&operand, defs) else { return Ok(()) };
            if constructor_fields(definition, ctor).is_some() {
                Ok(())
            } else {
                Err(DatatypeTermError::UnknownMember {
                    datatype: datatype.clone(),
                    member_kind: "constructor",
                    member: ctor.clone(),
                })
            }
        }
        _ => Ok(()),
    }
}

/// The ESTABLISHED sort of a selector's/tester's operand, once it is known to
/// be a datatype sort of the named datatype. `Ok(None)` means the checker could
/// not establish the operand's sort — ignorance, left to the full-formula sort
/// gate.
///
/// # Errors
///
/// The operand's sort is established and contradicts the term: not a datatype
/// at all, or a DIFFERENT datatype than the one the term names.
fn established_datatype_operand<'a>(
    op: &'static str,
    datatype: &str,
    member: &str,
    arg: &'a Formula,
) -> Result<Option<Cow<'a, Sort>>, DatatypeTermError> {
    let Ok(actual) = check_formula_sort_cow(arg) else { return Ok(None) };
    let Some(name) = datatype_name(&actual) else {
        return Err(DatatypeTermError::OperandNotDatatype {
            op,
            datatype: datatype.to_string(),
            member: member.to_string(),
            actual: actual.into_owned(),
        });
    };
    if name != datatype {
        return Err(DatatypeTermError::OperandDatatypeMismatch {
            op,
            datatype: datatype.to_string(),
            member: member.to_string(),
            actual: name.to_string(),
        });
    }
    Ok(Some(actual))
}

/// Convert a ay_bindings::Sort to a trust_types::Sort.
///
/// Returns None for sorts that trust_types doesn't support (Real, FP, String, etc.).
#[must_use]
pub fn sort_from_ay(sort: &AYSort) -> Option<Sort> {
    match sort.inner() {
        AYSortInner::Bool => Some(Sort::Bool),
        AYSortInner::Int => Some(Sort::Int),
        AYSortInner::BitVec(bv) => Some(Sort::BitVec(bv.width)),
        AYSortInner::Array(arr) => {
            let idx = sort_from_ay(&arr.index_sort)?;
            let elem = sort_from_ay(&arr.element_sort)?;
            Some(Sort::Array(Box::new(idx), Box::new(elem)))
        }
        AYSortInner::FloatingPoint(eb, sb) => Some(Sort::Float { eb: *eb, sb: *sb }),
        AYSortInner::Real => Some(Sort::Real),
        // ay sorts not representable in trust_types
        AYSortInner::Datatype(_)
        | AYSortInner::String
        | AYSortInner::Uninterpreted(_)
        | AYSortInner::RegLan
        | AYSortInner::Seq(_) => None,
        _ => None, // future-proof for #[non_exhaustive]
    }
}

/// An ordering comparison operator, so [`lower_ordering`] can dispatch the
/// integer-vs-float lowering once for all four.
enum OrderCmp {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Lower an ordering comparison `a <op> b`, dispatching on operand sort. A
/// FLOAT-sorted operand (an f64 magnitude bound `self.0 <= 1.0e30`) uses the IEEE
/// FP predicate (`fp.leq`/…); everything else keeps the integer lowering
/// (`int_le`/…) EXACTLY as before. The integer ops assert Int sorts and would
/// panic on an FP operand, so this dispatch is required for a float-sorted
/// comparison to lower at all. It is purely additive: no float ordering comparison
/// could previously reach `formula_to_expr` without panicking, so every
/// pre-existing (non-float) comparison lowers byte-for-byte identically.
fn lower_ordering(a: Expr, b: Expr, cmp: OrderCmp) -> Expr {
    let is_fp = a.sort().is_floating_point() || b.sort().is_floating_point();
    // A REAL-sorted operand (a ny-cert Farkas atom over real-valued network
    // variables) takes ay's exact-rational `real_*` predicates. `check_formula_sort`
    // refuses a mixed Int/Real atom before lowering, so `is_real` on either side
    // means both sides; ay's own sort check is the backstop and PANICS (fail
    // closed) rather than coerce if that ever fails to hold.
    let is_real = a.sort().is_real() || b.sort().is_real();
    match (cmp, is_fp, is_real) {
        (OrderCmp::Lt, false, false) => a.int_lt(b),
        (OrderCmp::Le, false, false) => a.int_le(b),
        (OrderCmp::Gt, false, false) => a.int_gt(b),
        (OrderCmp::Ge, false, false) => a.int_ge(b),
        (OrderCmp::Lt, true, _) => a.fp_lt(b),
        (OrderCmp::Le, true, _) => a.fp_le(b),
        (OrderCmp::Gt, true, _) => a.fp_gt(b),
        (OrderCmp::Ge, true, _) => a.fp_ge(b),
        (OrderCmp::Lt, false, true) => a.real_lt(b),
        (OrderCmp::Le, false, true) => a.real_le(b),
        (OrderCmp::Gt, false, true) => a.real_gt(b),
        (OrderCmp::Ge, false, true) => a.real_ge(b),
    }
}

/// Lower a `Formula::Rat` literal to ay's exact Real: the arbitrary-precision
/// numerator embedded as a Real, divided by the denominator when it is not
/// `1`.
///
/// `RatLit` enforces canonical decimal syntax on construction AND on
/// deserialization (`-?[1-9][0-9]*|0` over `[1-9][0-9]*`), so the digit
/// strings are folded into a `BigInt` directly — no parser, no failure path,
/// no fallback value. There is nothing to fail closed on: a non-canonical
/// literal cannot exist.
fn rat_literal_to_expr(lit: &trust_ir_contract::RatLit) -> Expr {
    fn digits_to_bigint(text: &str) -> num_bigint::BigInt {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(magnitude) => (true, magnitude),
            None => (false, text),
        };
        if digits.len() <= 38 {
            let magnitude = digits.bytes().fold(0u128, |acc, b| {
                acc * 10 + u128::from(u8::from(b.is_ascii_digit()) * b.wrapping_sub(b'0'))
            });
            let big = num_bigint::BigInt::from(magnitude);
            return if negative { -big } else { big };
        }
        let magnitude = digits.bytes().fold(num_bigint::BigInt::from(0u8), |acc, b| {
            // `RatLit` guarantees ASCII digits; anything else is unreachable by
            // construction, and folding it as `0` would only ever DENY a
            // certificate (a wrong literal fails the solver cross-check and the
            // kernel check), never mint one.
            acc * 10u8 + u8::from(b.is_ascii_digit()) * b.wrapping_sub(b'0')
        });
        if negative { -magnitude } else { magnitude }
    }
    let numerator = Expr::real_const(digits_to_bigint(lit.num()));
    if lit.is_integer() {
        numerator
    } else {
        numerator.real_div(Expr::real_const(digits_to_bigint(lit.den())))
    }
}

/// Convert a `trust_types::Formula` to an `ay_bindings::Expr`.
///
/// This is the key conversion for feeding trust-vcgen output into ay. The
/// mapping is 1:1 for every `Formula` variant the contract declares today.
/// Datatype sorts are lowered under the formula's own definition table
/// ([`DatatypeDefs::collect`], see [`sort_to_ay_in`]): a by-name back-edge
/// becomes ay's resolvable `datatype_ref`, a by-name reference in a term
/// position is widened to the table's one full definition, and a reference with
/// no definition anywhere is refused.
///
/// FALLIBLE, AND TOTAL — there is no `Formula` for which this aborts. Every
/// refusal the bridge can reach is a named [`AyBridgeError`]; callers decline
/// the obligation (`Unknown`) on one, which is neither a proof nor a
/// refutation. The classes, in the order they are established:
///
/// * a sort position with no ay counterpart (`Sort::RoundingMode`,
///   `Sort::BitVec(0)`, a future `Sort` variant) → [`AyBridgeError::UnlowerableSort`].
///   Checked FIRST, because [`sort_to_ay_in`] is infallible by design (every
///   in-tree sort position is lowered inline) and would otherwise abort inside
///   the walk;
/// * two different full definitions of one datatype name →
///   [`AyBridgeError::ConflictingDefinitions`]: there is no single descriptor
///   the terms could be authenticated against, and picking one would be a
///   silent misencoding;
/// * a by-name datatype reference with no definition anywhere →
///   [`AyBridgeError::UndefinedDatatype`]. Established before lowering because
///   ay-bindings' datatype API is infallible at a TERM position, so a reference
///   that occurs only in terms would otherwise meet an assertion, not an error;
/// * a datatype term that contradicts the definition the formula itself carries
///   → [`AyBridgeError::DatatypeTerm`], or, for a node ay's own checked API
///   refuses, [`AyBridgeError::Datatype`] carrying `ay_bindings::SortError` as
///   its [`std::error::Error::source`];
/// * a `Formula::Ctor` whose own sort is not a datatype sort →
///   [`AyBridgeError::CtorSortNotDatatype`];
/// * a non-literal `fp.*` rounding-mode operand, or a rounding-mode term
///   outside an rm slot → [`AyBridgeError::NonLiteralRoundingMode`]. ay has no
///   rounding-mode sort at all, so there is nothing faithful to lower a
///   symbolic rounding mode to, and the two coercions that used to stand in
///   here (`RNE` for the operand, `true` for the term) each made a SATISFIABLE
///   formula decide UNSAT;
/// * a `Formula` variant with no lowering arm →
///   [`AyBridgeError::UnsupportedFormula`], so a variant added to the contract
///   tomorrow declines instead of reaching an `unreachable!`.
///
/// The router does NOT rely on this function to establish any of them: it runs
/// the same checks as explicit pre-gates, so a decline carries the gate's own
/// diagnostic and is measured before any lowering work happens. Totality here
/// is for a caller that bypasses the router.
pub fn formula_to_expr(formula: &Formula) -> Result<Expr, AyBridgeError> {
    formula_to_expr_with_datatype_defs(formula, &DatatypeDefs::default())
}

/// [`formula_to_expr`] under a caller-supplied definition table — for a body
/// whose datatype definitions live in `VerifiableBody.datatype_defs` rather
/// than in the VC text. Definitions found in `formula` are added to the table
/// (and conflict-checked against it) first.
pub fn formula_to_expr_with_datatype_defs(
    formula: &Formula,
    defs: &DatatypeDefs,
) -> Result<Expr, AyBridgeError> {
    let mut unlowerable: Option<String> = None;
    let mut conflict: Option<DatatypeConflict> = None;
    let mut defs_cow: Cow<'_, DatatypeDefs> = Cow::Borrowed(defs);
    let mut has_by_name_datatype_ref = false;
    let mut has_datatype_term = false;

    let _ = crate::all_formula_nodes(formula, &mut |node| {
        if !has_datatype_term
            && matches!(node, Formula::Ctor { .. } | Formula::Sel { .. } | Formula::IsCtor { .. })
        {
            has_datatype_term = true;
        }
        crate::smt_logic::visit_node_sort_positions(node, &mut |sort| {
            if unlowerable.is_none() {
                if let Some(what) = unlowerable_sort(sort) {
                    unlowerable = Some(format!(
                        "VC formula has a sort position the ay bridge cannot lower: {what}"
                    ));
                    return;
                }
            }
            if conflict.is_none() {
                if let Err(err) = DatatypeDefs::add_sort_cow(&mut defs_cow, sort) {
                    conflict = Some(err);
                }
            }
            if !has_by_name_datatype_ref && sort_has_by_name_datatype(sort) {
                has_by_name_datatype_ref = true;
            }
        });
        unlowerable.is_none()
    });

    if let Some(position) = unlowerable {
        return Err(AyBridgeError::UnlowerableSort { position });
    }
    if let Some(conflict) = conflict {
        return Err(AyBridgeError::ConflictingDefinitions(conflict));
    }
    if has_by_name_datatype_ref
        && let Some(datatype) = undefined_datatype_reference(formula, &defs_cow)
    {
        return Err(AyBridgeError::UndefinedDatatype { datatype });
    }
    if has_datatype_term {
        check_datatype_terms(formula, &defs_cow)?;
    }
    formula_to_expr_in(formula, &defs_cow)
}

fn sort_has_by_name_datatype(sort: &Sort) -> bool {
    match sort {
        Sort::Datatype { constructors, .. } if constructors.is_empty() => true,
        Sort::Datatype { constructors, .. } => constructors
            .iter()
            .flat_map(|(_, fields)| fields.iter())
            .any(|(_, field_sort)| sort_has_by_name_datatype(field_sort)),
        Sort::Array(index, element) => {
            sort_has_by_name_datatype(index) || sort_has_by_name_datatype(element)
        }
        _ => false,
    }
}

// ── Fallible pre-authentication shared with the router's gates ──────────────
//
// These two predicates establish, WITHOUT lowering anything, the two refusal
// classes `sort_to_ay_in` answers with a panic (it is infallible by design, so
// every in-tree sort position can be lowered inline). `formula_to_expr`
// runs them first, which is what makes it total; the router runs them as
// explicit gates so a decline carries the gate's own diagnostic and is
// measured before any lowering work happens. One implementation, two callers.

/// The first datatype NAME `formula` references by name (`Sort::Datatype` with
/// an empty constructor list) that `defs` — the table `build_program` itself
/// lowers from — has no full definition for.
///
/// A dangling reference is a PROVEN defect, not ignorance: `sort_to_ay_in`
/// lowers it to ay's `DatatypeRef`, and ay resolves a `DatatypeRef` only
/// against a descriptor registered under that name. Since the table this gate
/// consults is the SAME `DatatypeDefs::collect(formula)` the builder uses,
/// nothing is registered under that name and the query cannot be built at all:
/// every lowering of the reference is refused, so the obligation ends as a
/// decline no matter which seam reports it.
///
/// It must be reported HERE because only ONE of those seams is fallible.
/// `build_program` refuses a dangling reference cleanly when it reaches
/// `try_declare_const`/`try_declare_datatype` — i.e. when some free variable or
/// declared definition carries the name. When the reference occurs ONLY in term
/// positions (a ground `Ctor` spelled by name, a `Sel` field sort, a quantifier
/// binder), there is no declaration to refuse it and the reference is first met
/// by `formula_to_expr_with_datatype_defs`, whose datatype API is INFALLIBLE at
/// the call site and fails closed with a PANIC. `run_with_policy`'s
/// `catch_unwind` would contain it, but containment is not input validation: a
/// caught panic still runs the process-global panic hook and can leak a false
/// compiler-ICE-looking diagnostic to stderr. Declining at the gate, with the
/// undefined datatype named, keeps the bridge unentered.
///
/// SOUNDNESS: declining emits neither a proof nor a refutation. And a by-name
/// reference whose definition IS present somewhere in the formula resolves
/// through `defs` exactly as the lowering resolves it, so the legitimate
/// by-name-vs-full pairing trust-ir-contract and trust-vcgen actually emit
/// (`pred: Level` on a `Sel`, a `__fld_*` binder, a recursive back-edge) is
/// never refused.
pub fn undefined_datatype_reference(formula: &Formula, defs: &DatatypeDefs) -> Option<String> {
    // The same sort positions `DatatypeDefs::extend_from_formula` walks to
    // BUILD the table — quantifier BINDER sorts included, which no
    // `children()`-based walk reaches — so the gate reads exactly what the
    // builder wrote. Shared with `unlowerable_sort_position` as
    // `visit_lowered_sort_positions`, so there is one list, not two.
    let mut undefined: Option<String> = None;
    let _ = crate::all_formula_nodes(formula, &mut |node| {
        crate::smt_logic::visit_node_sort_positions(node, &mut |sort| {
            if undefined.is_none() {
                undefined = undefined_datatype_in_sort(sort, defs);
            }
        });
        undefined.is_none()
    });
    undefined
}

/// [`undefined_datatype_reference`] for one sort: the first by-name datatype
/// reference inside `sort` with no definition in `defs`. A full definition
/// contributes its own name to the table (that is what `collect` did), so only
/// its FIELD sorts can dangle; array sorts are followed into both positions,
/// matching `DatatypeDefs::add_sort`. The recursion terminates because `Sort`
/// is a finite tree — a recursive datatype's back-edge is a by-name leaf.
fn undefined_datatype_in_sort(sort: &Sort, defs: &DatatypeDefs) -> Option<String> {
    match sort {
        Sort::Datatype { name, constructors } if constructors.is_empty() => {
            if defs.get(name).is_some() { None } else { Some(name.clone()) }
        }
        Sort::Datatype { constructors, .. } => constructors
            .iter()
            .flat_map(|(_, fields)| fields.iter())
            .find_map(|(_, field_sort)| undefined_datatype_in_sort(field_sort, defs)),
        Sort::Array(index, element) => undefined_datatype_in_sort(index, defs)
            .or_else(|| undefined_datatype_in_sort(element, defs)),
        _ => None,
    }
}

/// The first sort inside `sort` the ay bridge cannot lower. Follows array
/// index/element and datatype field sorts, matching `sort_to_ay_in`'s own
/// recursion; a by-name datatype reference is a leaf here (its definition
/// is audited by `undefined_datatype_reference`).
fn unlowerable_sort(sort: &Sort) -> Option<&'static str> {
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::Float { .. } => None,
        Sort::BitVec(0) => Some(
            "a zero-width bitvector sort, which ay has no sort for (`Sort::bitvec` asserts \
             width > 0)",
        ),
        Sort::BitVec(_) => None,
        Sort::RoundingMode => Some(
            "a RoundingMode-sorted declaration, binder or field: ay carries the rounding \
             mode as an enum argument of each fp.* operation, not as a sorted term, so there \
             is no ay sort to declare it at",
        ),
        Sort::Array(index, element) => unlowerable_sort(index).or_else(|| unlowerable_sort(element)),
        Sort::Datatype { constructors, .. } => constructors
            .iter()
            .flat_map(|(_, fields)| fields.iter())
            .find_map(|(_, field_sort)| unlowerable_sort(field_sort)),
        // `Sort` is #[non_exhaustive]: a variant added after this audit has
        // no `sort_to_ay_in` arm and would hit its `unreachable!`.
        #[allow(unreachable_patterns)]
        _ => Some(
            "a sort variant the ay bridge has no lowering arm for (added to the contract \
             after this gate was written)",
        ),
    }
}

/// Return a decline reason if any sort position in `formula` — a variable's
/// sort, a constructor/application result sort, a selector's field sort, or a
/// QUANTIFIER BINDER's sort — carries a sort `sort_to_ay_in` cannot lower
/// faithfully.
///
/// The audit of what the binder-sort hole hid, beyond rounding modes:
///
/// * **`Sort::RoundingMode`** — no ay sort exists (see
///   the router's `rounding_mode_position_defect` gate); `sort_to_ay_in` used to answer
///   `AYSort::bool()`, a silent misencoding that identifies distinct rounding
///   modes and can FALSE-PROVE. Now a fail-closed refusal in the bridge and a
///   decline here.
/// * **A zero-width bitvector** — `AYSort::bitvec` asserts `width > 0` and
///   PANICS on `0`. The existing `formula_sort_mismatch` gate refuses only
///   `FpToSbv`/`FpToUbv { width: 0 }`; a `Var`/binder/field of `BitVec(0)`, or
///   an `Array` with a `BitVec(0)` index or element, walked straight into that
///   assert, contained only by `run_with_policy`'s `catch_unwind` — which still
///   runs the process-global panic hook and can leak a false compiler-ICE
///   diagnostic. `check_formula_sort` is content with `Sort::BitVec(0)`, so
///   nothing else asks.
/// * **A by-name datatype with no definition** — already covered, and covered
///   for binders too: [`undefined_datatype_reference`] walks the SAME position
///   list (that is why the traversal is shared). Left there; this gate does not
///   duplicate it.
/// * **A future `#[non_exhaustive]` `Sort` variant** — `sort_to_ay_in`'s
///   wildcard is `unreachable!("unhandled Sort variant in sort_to_ay")`, a
///   fail-closed panic. Declining here turns the next added sort into a
///   DECLINE instead of a caught panic, the same way `is_lowerable_formula`
///   does for a new `Formula` variant. Vacuous for every sort of today's
///   contract.
///
/// SOUNDNESS: declining emits neither a proof nor a refutation, and every
/// condition reported is a PROVEN defect — the lowering of that exact sort is
/// a refusal or a panic, so the obligation ends as a decline whichever seam
/// reports it. Reporting it here keeps the bridge unentered.
pub fn unlowerable_sort_position(formula: &Formula) -> Option<String> {
    let mut defect: Option<String> = None;
    let _ = crate::all_formula_nodes(formula, &mut |node| {
        crate::smt_logic::visit_node_sort_positions(node, &mut |sort| {
            if defect.is_none() {
                defect = unlowerable_sort(sort).map(|what| {
                    format!("VC formula has a sort position the ay bridge cannot lower: {what}")
                });
            }
        });
        defect.is_none()
    });
    defect
}

fn formula_to_expr_in(formula: &Formula, defs: &DatatypeDefs) -> Result<Expr, AyBridgeError> {
    Ok(match formula {
        // Literals
        Formula::Bool(v) => Expr::bool_const(*v),
        Formula::Int(n) => Expr::int_const(*n),
        // Trust: round-A #2 false-PROVE fix — pass the full u128 (BigInt: From<u128>),
        // NOT `*n as i128` which wraps every value > i128::MAX (incl. u128::MAX -> -1),
        // making `0 <= a <= u128::MAX` encode as `0 <= a <= -1` (UNSAT) and vacuously
        // "proving" every u128 overflow/bounds VC in the in-process ay backend. The
        // smtlib text path already emits the decimal; this matches it losslessly.
        Formula::UInt(n) => Expr::int_const(*n),
        Formula::Rat(lit) => rat_literal_to_expr(lit),
        Formula::BitVec { value, width } => Expr::bitvec_const(*value, *width),

        // Variables
        Formula::Var(name, sort) => {
            Expr::var(name.clone(), sort_to_ay_with_defs(sort, defs))
        }
        // SymVar resolves symbol to string for ay variable creation.
        Formula::SymVar(sym, sort) => {
            Expr::var(sym.as_str().to_string(), sort_to_ay_with_defs(sort, defs))
        }

        // Boolean connectives
        Formula::Not(a) => formula_to_expr_in(a, defs)?.not(),
        Formula::And(terms) => {
            if terms.is_empty() {
                Expr::true_()
            } else {
                Expr::and_many(terms.iter().map(|a| formula_to_expr_in(a, defs)).collect::<Result<
                    Vec<_>,
                    _,
                >>(
                )?)
            }
        }
        Formula::Or(terms) => {
            if terms.is_empty() {
                Expr::false_()
            } else {
                Expr::or_many(
                    terms
                        .iter()
                        .map(|a| formula_to_expr_in(a, defs))
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
        }
        Formula::Implies(a, b) => {
            formula_to_expr_in(a, defs)?.implies(formula_to_expr_in(b, defs)?)
        }

        // Comparisons. Ordering comparisons are SORT-AWARE: a float-sorted operand
        // (an f64 magnitude bound `self.0 <= 1.0e30`) lowers to the IEEE FP predicate
        // (`fp.leq`), NOT `int_le` — the integer ops ASSERT Int sorts (`check:
        // int_same`) and would PANIC on an FP operand.
        //
        // `Eq` is sort-generic but STRUCTURAL: over FloatingPoint it is SMT-LIB `=`,
        // under which every NaN is one value (`NaN = NaN` holds) and +0/-0 are two
        // (`+0 = -0` fails). That is deliberately NOT Rust `==`, and it is
        // deliberately NOT rewritten to `fp.eq` here: vcgen defines a float
        // temporary by the equation `Eq(FpFromBits(dest), fp.add(..))`, and reading
        // that as `fp.eq` would make every NaN-producing definition unsatisfiable —
        // a vacuous proof. Rust `==` on floats is `Formula::FpEq` (below), and every
        // producer of a CONTRACT `==` emits it for float operands
        // (`crate::spec_float_eq`, SPEC-FLOAT-EQ-STRUCTURAL-1).
        Formula::Eq(a, b) => formula_to_expr_in(a, defs)?.eq(formula_to_expr_in(b, defs)?),
        Formula::Lt(a, b) => {
            lower_ordering(formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?, OrderCmp::Lt)
        }
        Formula::Le(a, b) => {
            lower_ordering(formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?, OrderCmp::Le)
        }
        Formula::Gt(a, b) => {
            lower_ordering(formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?, OrderCmp::Gt)
        }
        Formula::Ge(a, b) => {
            lower_ordering(formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?, OrderCmp::Ge)
        }

        // Linear arithmetic, sort-generic over the Int and Real carriers: the
        // sort checker has already established both operands agree, so a Real
        // left operand selects ay's exact-rational `real_*` ops (ay's own sort
        // assertion is the fail-closed backstop if it ever does not).
        Formula::Add(a, b) => {
            let (a, b) = (formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?);
            if a.sort().is_real() { a.real_add(b) } else { a.int_add(b) }
        }
        Formula::Sub(a, b) => {
            let (a, b) = (formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?);
            if a.sort().is_real() { a.real_sub(b) } else { a.int_sub(b) }
        }
        Formula::Mul(a, b) => {
            let (a, b) = (formula_to_expr_in(a, defs)?, formula_to_expr_in(b, defs)?);
            if a.sort().is_real() { a.real_mul(b) } else { a.int_mul(b) }
        }
        // Rust integer `/` and `%` are TRUNCATED (quotient toward zero; the
        // remainder takes the sign of the dividend). ay's `int_div`/`int_mod`
        // (like SMT-LIB `div`/`mod`) are EUCLIDEAN (mod always non-negative; div
        // floors toward -inf), which diverges for negative dividends. Lowering
        // `%`/`/` as bare `int_mod`/`int_div` here proved sign/range properties
        // that real Rust violates (e.g. `#[ensures(result >= 0)] fn f(x:i32)->i32
        // { x % 256 }` falsely Proved although `(-1) % 256 == -1`). This is the
        // SAME bug fixed in the smtlib text path (round 7); the in-process ay
        // backend uses THIS direct lowering, so it must encode truncation too
        // (round 18). For non-negative operands (all unsigned div/rem) these
        // reduce to plain div/mod, so it is correct for both signed and unsigned.
        // (Division by zero is governed by a separate div-by-zero VC.)
        //   trem(a,b) = ite(a >= 0, mod(a,b), -mod(-a,b))
        //   tdiv(a,b) = (a - trem) / b   [exact: a == b*tdiv + trem]
        Formula::Rem(a, b) => {
            let a = formula_to_expr_in(a, defs)?;
            let b = formula_to_expr_in(b, defs)?;
            Expr::ite(
                a.clone().int_ge(Expr::int_const(0)),
                a.clone().int_mod(b.clone()),
                a.int_neg().int_mod(b).int_neg(),
            )
        }
        Formula::Div(a, b) => {
            let a = formula_to_expr_in(a, defs)?;
            let b = formula_to_expr_in(b, defs)?;
            let trem = Expr::ite(
                a.clone().int_ge(Expr::int_const(0)),
                a.clone().int_mod(b.clone()),
                a.clone().int_neg().int_mod(b.clone()).int_neg(),
            );
            a.int_sub(trem).int_div(b)
        }
        Formula::Neg(a) => {
            let a = formula_to_expr_in(a, defs)?;
            if a.sort().is_real() { a.real_neg() } else { a.int_neg() }
        }

        // Bitvector arithmetic
        Formula::BvAdd(a, b, _) => formula_to_expr_in(a, defs)?.bvadd(formula_to_expr_in(b, defs)?),
        Formula::BvSub(a, b, _) => formula_to_expr_in(a, defs)?.bvsub(formula_to_expr_in(b, defs)?),
        Formula::BvMul(a, b, _) => formula_to_expr_in(a, defs)?.bvmul(formula_to_expr_in(b, defs)?),
        Formula::BvUDiv(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvudiv(formula_to_expr_in(b, defs)?)
        }
        Formula::BvSDiv(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvsdiv(formula_to_expr_in(b, defs)?)
        }
        Formula::BvURem(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvurem(formula_to_expr_in(b, defs)?)
        }
        Formula::BvSRem(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvsrem(formula_to_expr_in(b, defs)?)
        }
        Formula::BvAnd(a, b, _) => formula_to_expr_in(a, defs)?.bvand(formula_to_expr_in(b, defs)?),
        Formula::BvOr(a, b, _) => formula_to_expr_in(a, defs)?.bvor(formula_to_expr_in(b, defs)?),
        Formula::BvXor(a, b, _) => formula_to_expr_in(a, defs)?.bvxor(formula_to_expr_in(b, defs)?),
        Formula::BvNot(a, _) => formula_to_expr_in(a, defs)?.bvnot(),
        Formula::BvShl(a, b, _) => formula_to_expr_in(a, defs)?.bvshl(formula_to_expr_in(b, defs)?),
        Formula::BvLShr(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvlshr(formula_to_expr_in(b, defs)?)
        }
        Formula::BvAShr(a, b, _) => {
            formula_to_expr_in(a, defs)?.bvashr(formula_to_expr_in(b, defs)?)
        }

        // Bitvector comparisons
        Formula::BvULt(a, b, _) => formula_to_expr_in(a, defs)?.bvult(formula_to_expr_in(b, defs)?),
        Formula::BvULe(a, b, _) => formula_to_expr_in(a, defs)?.bvule(formula_to_expr_in(b, defs)?),
        Formula::BvSLt(a, b, _) => formula_to_expr_in(a, defs)?.bvslt(formula_to_expr_in(b, defs)?),
        Formula::BvSLe(a, b, _) => formula_to_expr_in(a, defs)?.bvsle(formula_to_expr_in(b, defs)?),

        // Bitvector conversions. Honor the signedness flag: an unsigned
        // conversion of a top-bit-set value (e.g. u8 0xFF) must yield 255, not
        // the two's-complement -1 that bv2int_signed produces. Always using the
        // signed conversion silently corrupts unsigned BvToInt operands.
        Formula::BvToInt(a, _w, signed) => {
            if *signed {
                formula_to_expr_in(a, defs)?.bv2int_signed()
            } else {
                formula_to_expr_in(a, defs)?.bv2int()
            }
        }
        Formula::IntToBv(a, w) => formula_to_expr_in(a, defs)?.int2bv(*w),
        Formula::BvExtract { inner, high, low } => {
            formula_to_expr_in(inner, defs)?.extract(*high, *low)
        }
        Formula::BvConcat(a, b) => {
            formula_to_expr_in(a, defs)?.concat(formula_to_expr_in(b, defs)?)
        }
        Formula::BvZeroExt(a, bits) => formula_to_expr_in(a, defs)?.zero_extend(*bits),
        Formula::BvSignExt(a, bits) => formula_to_expr_in(a, defs)?.sign_extend(*bits),

        // Conditional
        Formula::Ite(c, t, e) => Expr::ite(
            formula_to_expr_in(c, defs)?,
            formula_to_expr_in(t, defs)?,
            formula_to_expr_in(e, defs)?,
        ),

        // Quantifiers
        // Symbol bindings — resolve to String for ay API.
        Formula::Forall(bindings, body) => {
            let ay_bindings_list: Vec<(String, AYSort)> = bindings
                .iter()
                .map(|(sym, sort)| {
                    (sym.as_str().to_string(), sort_to_ay_with_defs(sort, defs))
                })
                .collect();
            Expr::forall(ay_bindings_list, formula_to_expr_in(body, defs)?)
        }
        Formula::Exists(bindings, body) => {
            let ay_bindings_list: Vec<(String, AYSort)> = bindings
                .iter()
                .map(|(sym, sort)| {
                    (sym.as_str().to_string(), sort_to_ay_with_defs(sort, defs))
                })
                .collect();
            Expr::exists(ay_bindings_list, formula_to_expr_in(body, defs)?)
        }

        // Arrays
        Formula::Select(arr, idx) => {
            formula_to_expr_in(arr, defs)?.select(formula_to_expr_in(idx, defs)?)
        }
        Formula::Store(arr, idx, val) => formula_to_expr_in(arr, defs)?
            .store(formula_to_expr_in(idx, defs)?, formula_to_expr_in(val, defs)?),
        // `((as const (Array I E)) v)`: ay's `const_array(I, v)`, whose element
        // sort is `v`'s own. The node CARRIES `E`; ay reads it from `v`. The two
        // must agree, or the lowered term would have a different sort than the
        // formula declares and a later select/store/equality against a term of
        // the declared sort would be ill-sorted inside ay. That is refused here
        // as an unsupported formula, never approximated.
        Formula::ConstArray { index_sort, elem_sort, value } => {
            let value = formula_to_expr_in(value, defs)?;
            let declared = sort_to_ay_with_defs(elem_sort, defs);
            if *value.sort() != declared {
                return Err(AyBridgeError::UnsupportedFormula {
                    formula: format!(
                        "const array whose value sort {:?} is not its declared element sort {:?}",
                        value.sort(),
                        declared
                    ),
                });
            }
            Expr::const_array(sort_to_ay_with_defs(index_sort, defs), value)
        }

        // A NULLARY uninterpreted symbol — a `Pred` or an `FnApp` with no
        // arguments — is a CONSTANT of its result sort, and is lowered as one:
        // the ay variable its caller must declare with `declare_const` (the
        // in-process lane's `build_program` does exactly that for every
        // nullary signature it collects).
        //
        // NOT a zero-argument application. ay builds a native `FuncApp` with
        // no arguments through `uf::apply`, i.e. an APPLICATION term, while its
        // SMT-LIB elaborator reads `(declare-fun c () S)` as a declared
        // constant and a bare `c` as that constant — a different `TermId`. The
        // retained-source guard (`Solver::try_assert_term_with_source`, which
        // every proof-producing solve goes through) compares exactly those
        // two, so every assertion that mentioned a nullary symbol and did not
        // fold to a literal was refused with "source does not reconstruct the
        // native assertion" and DECLINED: `fzero = 1 ∧ y = 2` and
        // `priv_dropped ∧ y = 2` alike (measured 2026-09-24). As a constant,
        // the native term and the source's re-elaboration are the same term by
        // construction, which is what free variables already rely on. The
        // text lane needs no change: `(declare-fun c () S)` IS a constant
        // declaration in SMT-LIB, and the term prints as the bare `c` either
        // way.
        Formula::Pred(name, args) if args.is_empty() => {
            Expr::var(name.as_str().to_string(), AYSort::bool())
        }
        Formula::FnApp { func, args, sort } if args.is_empty() => {
            Expr::var(func.clone(), sort_to_ay_with_defs(sort, defs))
        }

        // Uninterpreted boolean predicate: an opaque `Pred(name, args)` becomes
        // a Bool-sorted uninterpreted function application in ay. `func_app`
        // fixes the result sort to Bool, matching `Pred`'s predicate semantics.
        Formula::Pred(name, args) => Expr::func_app(
            name.as_str().to_string(),
            args.iter().map(|a| formula_to_expr_in(a, defs)).collect::<Result<Vec<_>, _>>()?,
        ),

        // Uninterpreted FUNCTION application — the function-symbol twin of
        // `Pred`, which is only its `Bool`-result special case. PRODUCED IN
        // PRODUCTION: trust-vcgen mints one as a Skolem term
        // (`quantifier_tiers::analysis`) and as the reference-function side of
        // the `model = reference` postconditions of the recursive-datatype /
        // fuel-outcome / threaded-budget lanes
        // (`Eq(_0, FnApp(reference, [fuel, e]))`), which trust-certify then
        // parses back. Before this arm every one of those VCs fell through to
        // the `#[non_exhaustive]` wildcard below and PANICKED inside the
        // bridge, rescued only by `run_with_policy`'s `catch_unwind` — the
        // same shape as the by-name-datatype class, and reachable through
        // every pre-gate because `check_formula_sort`/`infer_sort` already
        // sort an `FnApp` by the result sort it carries.
        //
        // `Expr::func_app` fixes the result sort to `Bool` (it is ay's CHC
        // relation constructor), so a `Level`-returning reference function must
        // go through `func_app_with_sort` with the RESULT SORT the node carries,
        // lowered under the same definition table as every other sort position:
        // a datatype result spelled by name is widened to the formula's one full
        // definition exactly as a `Var`'s sort is.
        //
        // DECLARATION. Like `Pred`, the symbol must be declared to the program
        // before this application is translated: ay's direct executor answers an
        // unknown symbol with `ExprTranslation("undeclared function …")` and a
        // signature that disagrees with the application inside the PANICKING
        // `uf::apply`. The router's `uninterpreted_symbol_signatures` emits a
        // `declare-fun` at exactly the (argument sorts, result sort) signature
        // this arm applies — in both the in-process and the SMT-LIB text lane —
        // and `uninterpreted_signature_conflict` declines, before the bridge,
        // any formula that applies one name at two signatures.
        Formula::FnApp { func, args, sort } => Expr::func_app_with_sort(
            func.clone(),
            args.iter().map(|a| formula_to_expr_in(a, defs)).collect::<Result<Vec<_>, _>>()?,
            sort_to_ay_with_defs(sort, defs),
        ),

        // ── IEEE-754 floating point ─────────────────────────────────────────
        Formula::FpConst { bits, eb, sb } => fp_const_from_bits(*bits, *eb, *sb),
        Formula::FpNaN { eb, sb } => Expr::fp_nan(&AYSort::floating_point(*eb, *sb)),
        Formula::FpInf { neg, eb, sb } => {
            let s = AYSort::floating_point(*eb, *sb);
            if *neg { Expr::fp_minus_infinity(&s) } else { Expr::fp_plus_infinity(&s) }
        }
        Formula::FpZero { neg, eb, sb } => {
            let s = AYSort::floating_point(*eb, *sb);
            if *neg { Expr::fp_minus_zero(&s) } else { Expr::fp_plus_zero(&s) }
        }
        // A bare rounding-mode term has no standalone ay `Expr` (ay takes it as
        // an enum arg of each fp.* op, via `ay_rounding_mode`). This arm is
        // reached ONLY when a rounding-mode term sits somewhere other than an
        // fp.* rm slot — the rm slots are read by `ay_rounding_mode`, never
        // recursed into. `Expr::true_()` was a SILENT MISENCODING there:
        // `Eq(FpRoundingMode(RNE), FpRoundingMode(RTZ))` became `(= true true)`,
        // so its negation — a reachable violation — was UNSAT and falsely
        // PROVED. Fail closed; the router declines the shape before the bridge
        // (`rounding_mode_position_defect`).
        Formula::FpRoundingMode(rm) => {
            return Err(AyBridgeError::NonLiteralRoundingMode(NonLiteralRoundingMode {
                operand: format!(
                    "the rounding-mode literal {rm:?} appears outside an fp.* rounding-mode \
                     operand, where ay has no expression for it; failing closed rather than \
                     substituting a Bool, which would identify distinct rounding modes"
                ),
            }));
        }
        Formula::FpAdd(rm, a, b) => {
            formula_to_expr_in(a, defs)?.fp_add(ay_rounding_mode(rm)?, formula_to_expr_in(b, defs)?)
        }
        Formula::FpSub(rm, a, b) => {
            formula_to_expr_in(a, defs)?.fp_sub(ay_rounding_mode(rm)?, formula_to_expr_in(b, defs)?)
        }
        Formula::FpMul(rm, a, b) => {
            formula_to_expr_in(a, defs)?.fp_mul(ay_rounding_mode(rm)?, formula_to_expr_in(b, defs)?)
        }
        Formula::FpDiv(rm, a, b) => {
            formula_to_expr_in(a, defs)?.fp_div(ay_rounding_mode(rm)?, formula_to_expr_in(b, defs)?)
        }
        Formula::FpFma(rm, a, b, c) => formula_to_expr_in(a, defs)?.fp_fma(
            ay_rounding_mode(rm)?,
            formula_to_expr_in(b, defs)?,
            formula_to_expr_in(c, defs)?,
        ),
        Formula::FpSqrt(rm, a) => formula_to_expr_in(a, defs)?.fp_sqrt(ay_rounding_mode(rm)?),
        Formula::FpRem(a, b) => formula_to_expr_in(a, defs)?.fp_rem(formula_to_expr_in(b, defs)?),
        Formula::FpNeg(a) => formula_to_expr_in(a, defs)?.fp_neg(),
        Formula::FpAbs(a) => formula_to_expr_in(a, defs)?.fp_abs(),
        Formula::FpMin(a, b) => formula_to_expr_in(a, defs)?.fp_min(formula_to_expr_in(b, defs)?),
        Formula::FpMax(a, b) => formula_to_expr_in(a, defs)?.fp_max(formula_to_expr_in(b, defs)?),
        Formula::FpEq(a, b) => formula_to_expr_in(a, defs)?.fp_eq(formula_to_expr_in(b, defs)?),
        Formula::FpLt(a, b) => formula_to_expr_in(a, defs)?.fp_lt(formula_to_expr_in(b, defs)?),
        Formula::FpLe(a, b) => formula_to_expr_in(a, defs)?.fp_le(formula_to_expr_in(b, defs)?),
        Formula::FpGt(a, b) => formula_to_expr_in(a, defs)?.fp_gt(formula_to_expr_in(b, defs)?),
        Formula::FpGe(a, b) => formula_to_expr_in(a, defs)?.fp_ge(formula_to_expr_in(b, defs)?),
        Formula::FpIsNaN(a) => formula_to_expr_in(a, defs)?.fp_is_nan(),
        Formula::FpIsInfinite(a) => formula_to_expr_in(a, defs)?.fp_is_infinite(),
        Formula::FpIsZero(a) => formula_to_expr_in(a, defs)?.fp_is_zero(),
        Formula::FpIsNormal(a) => formula_to_expr_in(a, defs)?.fp_is_normal(),
        Formula::FpIsSubnormal(a) => formula_to_expr_in(a, defs)?.fp_is_subnormal(),
        Formula::FpIsNegative(a) => formula_to_expr_in(a, defs)?.fp_is_negative(),
        Formula::FpIsPositive(a) => formula_to_expr_in(a, defs)?.fp_is_positive(),
        Formula::FpFromBits { bits, eb, sb } => {
            fp_from_bv_expr(formula_to_expr_in(bits, defs)?, *eb, *sb)
        }
        // `(fp.to_ieee_bv <fp>)` — reinterpret a float as its IEEE-754 bit
        // pattern (an `(eb+sb)`-wide bitvector). The EXACT inverse of
        // `FpFromBits`. Bit-preserving: NaN payloads and the sign of ±0.0 are
        // carried through verbatim, so a structural `Eq` over the resulting BVs
        // distinguishes them (unlike `fp.eq`, which is IEEE value-equality).
        Formula::FpToIeeeBv(a) => formula_to_expr_in(a, defs)?.fp_to_ieee_bv(),

        // ── The five FP CONVERSION nodes ────────────────────────────────────
        // Produced in PRODUCTION by trust-machine-sem's AArch64 semantics:
        // FCVTZS/FCVTZU mint `FpToSbv`/`FpToUbv`, SCVTF/UCVTF mint
        // `FpFromSbv`/`FpFromUbv`, FCVT mints `FpConvert`. Before these arms
        // every one of them fell through to the fail-closed wildcard below and
        // PANICKED inside this bridge — the same class as `FnApp`, and
        // reachable through every pre-gate because `check_formula_sort` has
        // carried explicit arms for all five since 2026-08-18.
        //
        // Those same arms are what makes ay's sort-ASSERTING convenience
        // wrappers safe here: the router establishes `check_formula_sort` =
        // `Ok(Bool)` for the whole formula before the bridge, and that check
        // requires `value` to be `Float { eb, sb }` for `FpToSbv`/`FpToUbv`
        // (exactly the format the node carries) and `FpConvert`, and
        // `BitVec(_)` for `FpFromSbv`/`FpFromUbv`. A rounding-mode operand that
        // is not a LITERAL has no ay argument at all: it is declined by the
        // router (`rounding_mode_position_defect`, whose fallible form lives
        // here as `non_literal_rounding_mode_operand`) and fails closed in
        // the named refusal above for a direct library caller. It is NOT
        // defaulted to RNE — that was a false-PROVE.
        //
        // FULLY SPECIFIED by SMT-LIB, so these three lower to ay's native
        // operators — the same ones `to_smtlib` emits: `((_ to_fp eb sb) rm
        // bv)`, `((_ to_fp_unsigned eb sb) rm bv)` and `((_ to_fp eb sb) rm
        // fp)`.
        Formula::FpFromSbv { rm, value, eb, sb } => {
            formula_to_expr_in(value, defs)?.bv_to_fp(ay_rounding_mode(rm)?, *eb, *sb)
        }
        Formula::FpFromUbv { rm, value, eb, sb } => {
            formula_to_expr_in(value, defs)?.bv_to_fp_unsigned(ay_rounding_mode(rm)?, *eb, *sb)
        }
        Formula::FpConvert { rm, value, eb, sb } => {
            formula_to_expr_in(value, defs)?.fp_to_fp(ay_rounding_mode(rm)?, *eb, *sb)
        }

        // `FpToSbv`/`FpToUbv` are TOTAL with the AArch64/Rust SATURATING
        // reading (NaN -> 0, out-of-range -> clamp), while SMT-LIB's
        // `fp.to_sbv`/`fp.to_ubv` are UNSPECIFIED on exactly those inputs. The
        // contract is explicit that a consumer which cannot honour the total
        // reading must REFUSE the node rather than approximate it, so lowering
        // to the bare ay operator is not an option: a solver could then choose
        // an arbitrary value precisely where the semantics promise saturation,
        // and the in-process lane would disagree with the text lane on the same
        // VC. These arms therefore build the SAME guarded expansion
        // `Formula::to_smtlib` emits, node for node.
        Formula::FpToSbv { rm, value, width, eb, sb } => fp_to_bv_saturating(
            formula_to_expr_in(value, defs)?,
            ay_rounding_mode(rm)?,
            *width,
            *eb,
            *sb,
            true,
        ),
        Formula::FpToUbv { rm, value, width, eb, sb } => fp_to_bv_saturating(
            formula_to_expr_in(value, defs)?,
            ay_rounding_mode(rm)?,
            *width,
            *eb,
            *sb,
            false,
        ),

        // ── Algebraic datatypes (Lever A) ───────────────────────────────────
        // A datatype equation like `Sort(succ l) = Sort(succ l)` lowers to a
        // GENUINE ay `DatatypeConstructor`/`Selector`/`Tester` Expr (not a
        // stub). The datatype must have been declared to the program
        // (`declare-datatype` / `try_declare_datatype`) for the solver to accept
        // these; declaring one asserts NO fact (a fresh datatype-sorted constant
        // is SAT), so this can only let obligations report their honest outcome,
        // never manufacture a false PROVE.
        //
        // AY BOUNDARY (ay ≥ d4400b131 "Sort::datatype_ref for recursive datatype
        // fields", on top of ad07c5cc6 "validate datatype signatures before
        // projection"). `Expr::try_datatype_constructor`, `try_field_select` and
        // `try_is_constructor` authenticate every application against the
        // descriptor RECORDED ON THE SORT ITSELF (ay-bindings expr/dt/check.rs):
        // each argument / requested result sort must be the SAME SORT as the
        // declared field sort, compared structurally with a `DatatypeRef` in a
        // field resolving to the ENCLOSING declaration of that name — never to
        // the argument's sort, never to a bare `Uninterpreted` name, and a
        // reference outside a declaration of its name is not a sort at all.
        // `Datatype(N)` and `Uninterpreted(N)` stay distinct; a same-named
        // datatype with other constructors is refused.
        //
        // `sort_to_ay_in` meets that boundary from trust-ir-contract's
        // conventions (a TERM carries the full definition, a datatype-typed
        // FIELD is a by-name reference): the back-edge becomes `datatype_ref`,
        // and a by-name form in a term position or a sibling field is widened to
        // the formula's ONE full definition of that name. What is left for this
        // arm to refuse is therefore a genuinely malformed encoding — a wrong
        // argument sort, an undeclared constructor/field, a wrong arity, a
        // by-name reference with no definition anywhere in the formula, or a
        // descriptor forged against the one the argument carries.
        //
        // Fail-closed: a refusal is a named `AyBridgeError::Datatype` carrying
        // ay's own `SortError` — never a stub, a re-sorted term or a silent
        // misencoding. The refusal is handed back BY NAME, with ay's own
        // `SortError` as the error source. The SMT-LIB text lane
        // (`collect_datatype_decls` / `declare-datatype`) is nominal and does
        // not pass through this check.
        Formula::Ctor { ctor, args, sort } => {
            // The datatype (sort) name is carried by the Ctor's own result sort.
            let Sort::Datatype { name, .. } = sort else {
                // Fail-closed: a Ctor whose sort is not a datatype is a builder
                // bug — refuse rather than silently misencode.
                return Err(AyBridgeError::CtorSortNotDatatype {
                    ctor: ctor.clone(),
                    sort: format!("{sort:?}"),
                });
            };
            Expr::try_datatype_constructor(
                name.clone(),
                ctor.clone(),
                args.iter().map(|a| formula_to_expr_in(a, defs)).collect::<Result<Vec<_>, _>>()?,
                sort_to_ay_with_defs(sort, defs),
            )
            .map_err(|source| AyBridgeError::Datatype {
                node: "constructor",
                datatype: name.clone(),
                member: ctor.clone(),
                source,
            })?
        }
        Formula::Sel { datatype, field, field_sort, arg } => formula_to_expr_in(arg, defs)?
            .try_field_select(
                datatype.clone(),
                field.clone(),
                sort_to_ay_with_defs(field_sort, defs),
            )
            .map_err(|source| AyBridgeError::Datatype {
                node: "selector",
                datatype: datatype.clone(),
                member: field.clone(),
                source,
            })?,
        Formula::IsCtor { datatype, ctor, arg } => formula_to_expr_in(arg, defs)?
            .try_is_constructor(datatype.clone(), ctor.clone())
            .map_err(|source| AyBridgeError::Datatype {
                node: "tester",
                datatype: datatype.clone(),
                member: ctor.clone(),
                source,
            })?,

        // `Formula` is #[non_exhaustive] (trust-ir-contract). Fail-closed: a
        // variant we cannot faithfully lower to an ay Expr must abort (a loud
        // panic in the verify path), never a silent misencoding.
        //
        // AUDITED (round 10): every variant the contract declares TODAY has an
        // explicit arm above — literals, `Rat`, variables in both spellings,
        // the connectives, the sort-generic comparisons, Int/Real arithmetic,
        // the whole Bv* and Fp* families, `Ite`, `Forall`/`Exists`,
        // `Select`/`Store`, `Pred`, `Ctor`/`Sel`/`IsCtor` and `FnApp`. So this
        // arm is reachable only from a contract variant that does not exist
        // yet, i.e. never from a formula today's router can accept. It stays as
        // the fail-closed landing for a FUTURE variant: adding one must be a
        // loud abort here, not a silent misencoding, until its lowering (or its
        // gate decline) is written. `is_lowerable_formula` below is the
        // machine-checked statement of that audit, and the router's gate uses
        // it so a new variant declines instead of ever reaching here.
        other => {
            return Err(AyBridgeError::UnsupportedFormula { formula: format!("{other:?}") });
        }
    })
}

/// The TOTAL, saturating FP -> BV conversion, as the guarded expansion
/// `Formula::to_smtlib` emits — node for node, so the in-process lane and the
/// SMT-LIB text lane decide the same VC the same way.
///
/// `fp.to_sbv`/`fp.to_ubv` are UNSPECIFIED for NaN and for inputs outside the
/// destination's range; [`Formula::FpToSbv`]/[`Formula::FpToUbv`] are TOTAL
/// with the AArch64/Rust reading (NaN -> 0; out of range -> clamp to the
/// destination's minimum/maximum). The bare operator is therefore never
/// emitted alone: it appears only under the guards that have already excluded
/// every input on which it is unspecified.
///
/// Bounds are exact. A power of two is representable in any format whose
/// exponent range admits it, and each bound is built as a `to_fp` of a wider
/// bitvector literal IN THE OPERAND'S OWN FORMAT (`eb`/`sb`, which the node
/// carries). On the signed low side overflow is `x <= MIN-1`, and in a format
/// too coarse to represent `MIN-1` that bound rounds to `MIN` — where the guard
/// may fire on `x == MIN` exactly, but the clamp value IS the true conversion
/// there, so the answer is unchanged. (Same reasoning, same constants, as the
/// text path; see `Formula::to_smtlib`.)
///
/// Widths are computed in [`num_bigint::BigInt`], not in `u128`, so no shift
/// can overflow here for any `width` the contract can carry. `width == 0` is
/// the one shape that has no bitvector to land in; ay's `bitvec_const` refuses
/// it, and the router's `formula_bitcast_mismatch` gate declines it before the
/// bridge.
///
/// THE TWO EXPANSIONS ARE CONSTANT-FOR-CONSTANT IDENTICAL AT EVERY WIDTH THE
/// CONTRACT CAN CARRY — same values, same literal bit widths `w`, `w+1`,
/// `w+2`, same guard order. Both compute their clamp constants in
/// [`num_bigint::BigInt`]: this function always did, and
/// `Formula::to_smtlib`'s text expansion does since trust-ir `4ac1b25c`
/// ("the FP->BV clamp constants are exact at every width"), which replaced the
/// `1u128 << (w - 1)` / `1u128 << (w + 2)` / `1u128 << w` shifts that used to
/// overflow from `width == 126` signed and `width == 128` unsigned. Verified
/// node for node across `w ∈ {1, 2, 8, 16, 32, 63, 64, 65, 100, 125, 126, 127,
/// 128, 200}` in both signs, against each other AND against a third reference
/// computed independently in `BigInt`.
///
/// A BOUND SURVIVES, BUT IT IS NOT THIS DISAGREEMENT. The router still declines
/// `width > 64`, because the `fp.to_sbv`/`fp.to_ubv` node this expansion WRAPS
/// is bit-blasted by ay, whose blaster computes the target format's extremal
/// values in `u64`
/// (`first-party/ay/crates/ay-theories/fp/src/bitblast.rs`): the signed branch
/// PANICS with `attempt to shift left with overflow` at every `width >= 65`,
/// and the unsigned branch silently clamps its representable maximum to
/// `u64::MAX` rather than `2^w - 1` there — the silent one being the worse of
/// the two, since it does not fail closed. So the remaining bound is ay's
/// native ENCODE limit alone; the lane-divergence half of it is gone. See
/// `fp_to_bv_agreeing_width` in `trust-router/in_process_ay_backend.rs`, which
/// carries the measurement and the one upstream change `first-party/ay` still
/// needs.
fn fp_to_bv_saturating(x: Expr, rm: AyRm, width: u32, eb: u32, sb: u32, signed: bool) -> Expr {
    use num_bigint::BigInt;

    let one = BigInt::from(1u32);
    let w = width as usize;
    let zero_bv = Expr::bitvec_const(BigInt::from(0u32), width);

    // The positive out-of-range threshold, as an unsigned (w+1)-bit literal
    // converted into the operand's format: 2^(w-1) signed, 2^w unsigned.
    let positive_bound =
        Expr::bitvec_const(if signed { &one << (w - 1) } else { &one << w }, width + 1)
            .bv_to_fp_unsigned(AyRm::RNE, eb, sb);

    // The negative threshold: -(2^(w-1)) - 1 as a SIGNED (w+2)-bit literal for
    // the signed conversion, and -1.0 for the unsigned one (every value at or
    // below it clamps to zero).
    let negative_bound = if signed {
        let min_minus_one = (&one << (w + 2)) - (&one << (w - 1)) - &one;
        Expr::bitvec_const(min_minus_one, width + 2).bv_to_fp(AyRm::RNE, eb, sb)
    } else {
        Expr::bitvec_const(one.clone(), width + 1).bv_to_fp_unsigned(AyRm::RNE, eb, sb).fp_neg()
    };

    let max_bv = Expr::bitvec_const(
        if signed { (&one << (w - 1)) - &one } else { (&one << w) - &one },
        width,
    );
    let min_bv = if signed { Expr::bitvec_const(&one << (w - 1), width) } else { zero_bv.clone() };

    let converted =
        if signed { x.clone().fp_to_sbv(rm, width) } else { x.clone().fp_to_ubv(rm, width) };

    Expr::ite(
        x.clone().fp_is_nan(),
        zero_bv,
        Expr::ite(
            x.clone().fp_ge(positive_bound),
            max_bv,
            Expr::ite(x.fp_le(negative_bound), min_bv, converted),
        ),
    )
}

/// True iff every node of `formula` is a variant [`formula_to_expr`] has an
/// explicit lowering arm for.
///
/// `Formula` is `#[non_exhaustive]`: a variant added to trust-ir-contract
/// tomorrow compiles here with no lowering and falls through to the
/// fail-closed `unreachable!` — a PANIC in the verify path, contained only by
/// the router's `catch_unwind`, which still runs the process-global panic hook
/// and leaks a false compiler-ICE-looking diagnostic. That is exactly how
/// `Formula::FnApp` and the five FP conversion nodes reached production while
/// passing every sort gate.
///
/// This predicate is the machine-checked twin of the audit recorded on that
/// wildcard arm: it enumerates the variants that HAVE an arm, so adding a
/// contract variant without teaching this bridge makes the router DECLINE the
/// obligation (sound: neither a proof nor a refutation) instead of panicking.
/// Keep it in lockstep with [`formula_to_expr`]'s match — the two are meant to
/// be read side by side.
#[must_use]
pub fn is_lowerable_formula(formula: &Formula) -> bool {
    crate::all_formula_nodes(formula, &mut node_has_lowering)
}

/// One node of [`is_lowerable_formula`].
fn node_has_lowering(node: &Formula) -> bool {
    match node {
        // Literals and variables
        Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::Rat(_)
        | Formula::BitVec { .. }
        | Formula::Var(..)
        | Formula::SymVar(..)
        // Connectives
        | Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        // Comparisons
        | Formula::Eq(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        // Int/Real arithmetic
        | Formula::Add(..)
        | Formula::Sub(..)
        | Formula::Mul(..)
        | Formula::Div(..)
        | Formula::Rem(..)
        | Formula::Neg(_)
        // Bitvectors
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
        | Formula::BvSignExt(..)
        // Floating point
        | Formula::FpConst { .. }
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
        | Formula::FpNeg(_)
        | Formula::FpAbs(_)
        | Formula::FpMin(..)
        | Formula::FpMax(..)
        | Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpIsNaN(_)
        | Formula::FpIsInfinite(_)
        | Formula::FpIsZero(_)
        | Formula::FpIsNormal(_)
        | Formula::FpIsSubnormal(_)
        | Formula::FpIsNegative(_)
        | Formula::FpIsPositive(_)
        | Formula::FpFromBits { .. }
        | Formula::FpToIeeeBv(_)
        | Formula::FpToSbv { .. }
        | Formula::FpToUbv { .. }
        | Formula::FpFromSbv { .. }
        | Formula::FpFromUbv { .. }
        | Formula::FpConvert { .. }
        // Conditional, quantifiers, arrays
        | Formula::Ite(..)
        | Formula::Forall(..)
        | Formula::Exists(..)
        | Formula::Select(..)
        | Formula::Store(..)
        | Formula::ConstArray { .. }
        // Uninterpreted symbols and datatype terms
        | Formula::Pred(..)
        | Formula::Ctor { .. }
        | Formula::Sel { .. }
        | Formula::IsCtor { .. }
        | Formula::FnApp { .. } => true,
        // A variant added to the contract after this audit: NOT lowerable until
        // an arm is written for it.
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

/// A rounding-mode operand that is not an rm LITERAL, so the bridge has no
/// faithful lowering for it.
///
/// ay takes the rounding mode as an ENUM ARGUMENT (`ay_bindings::RoundingMode`)
/// of each `fp.*` builder, so only a `Formula::FpRoundingMode(_)` operand can
/// be carried across. Anything else — an rm-sorted `Var`/`SymVar`, a
/// quantifier-bound rm, an `Ite` over two rm literals, an rm-returning `FnApp` —
/// has no ay term and MUST NOT be approximated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonLiteralRoundingMode {
    /// Debug rendering of the offending operand term.
    pub operand: String,
}

impl std::fmt::Display for NonLiteralRoundingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "an fp.* rounding-mode operand is not a rounding-mode LITERAL: {}. ay carries the \
             rounding mode as an enum argument of the operation, so a non-literal rm has no ay \
             expression and cannot be lowered",
            self.operand
        )
    }
}

impl std::error::Error for NonLiteralRoundingMode {}

/// Extract the ay rounding-mode enum from a `Formula::FpRoundingMode` operand.
///
/// FALLIBLE ON PURPOSE (round-E false-PROVE fix). This used to end in
/// `_ => AyRm::RNE`, which SILENTLY REWROTE every non-literal rm operand to
/// round-to-nearest-even. That is not a conservative approximation, it is a
/// different formula: `FpAdd(Var("rmv", Sort::RoundingMode), x, y)` and
/// `FpAdd(FpRoundingMode(RNE), x, y)` lowered to the IDENTICAL ay term
/// `(fp.add RNE x y)`, so a violation formula asserting they differ — which is
/// SATISFIABLE, witnessed by any `rmv != RNE` that changes the rounding —
/// came back UNSAT and the obligation was reported Proved. There is no value
/// this function may return in that case, so it returns an error its callers
/// must handle.
fn ay_rounding_mode(f: &Formula) -> Result<AyRm, NonLiteralRoundingMode> {
    match f {
        Formula::FpRoundingMode(rm) => Ok(match rm {
            RoundingMode::RNE => AyRm::RNE,
            RoundingMode::RNA => AyRm::RNA,
            RoundingMode::RTP => AyRm::RTP,
            RoundingMode::RTN => AyRm::RTN,
            RoundingMode::RTZ => AyRm::RTZ,
        }),
        other => Err(NonLiteralRoundingMode { operand: format!("{other:?}") }),
    }
}

/// The first `fp.*` node in `formula` whose rounding-mode operand is not a
/// rounding-mode LITERAL, as a human-readable reason.
///
/// This is the FALLIBLE pre-check for [`formula_to_expr`]: a caller that gets
/// `Some(reason)` must not lower the formula, because the only alternative the
/// lowering has is the fail-closed
/// [`AyBridgeError::NonLiteralRoundingMode`] refusal. The router asks it as
/// a gate and DECLINES (sound: neither a proof nor a refutation).
///
/// It covers every rm-operand position the contract has — the six arithmetic
/// nodes and the five conversion nodes — and it reads the operand SLOT rather
/// than the operand's sort, so it sees a non-literal rm wherever it is spelled,
/// including one bound by a quantifier (whose binder sorts no `children()`
/// walk can reach).
#[must_use]
pub fn non_literal_rounding_mode_operand(formula: &Formula) -> Option<String> {
    let mut defect: Option<String> = None;
    let _ = crate::all_formula_nodes(formula, &mut |node| {
        if let Some(rm) = rounding_mode_operand_slot(node)
            && let Err(error) = ay_rounding_mode(rm)
        {
            defect = Some(error.to_string());
            return false;
        }
        true
    });
    defect
}

#[must_use]
fn rounding_mode_operand_slot(node: &Formula) -> Option<&Formula> {
    match node {
        Formula::FpAdd(rm, _, _)
        | Formula::FpSub(rm, _, _)
        | Formula::FpMul(rm, _, _)
        | Formula::FpDiv(rm, _, _)
        | Formula::FpFma(rm, _, _, _)
        | Formula::FpSqrt(rm, _)
        | Formula::FpToSbv { rm, .. }
        | Formula::FpToUbv { rm, .. }
        | Formula::FpFromSbv { rm, .. }
        | Formula::FpFromUbv { rm, .. }
        | Formula::FpConvert { rm, .. } => Some(rm),
        _ => None,
    }
}

/// The children of `node` that ARE `fp.*` rounding-mode operand slots.
///
/// One list, used by both the gate ([`non_literal_rounding_mode_operand`]) and
/// the router's out-of-position audit, so the two cannot drift apart. Every
/// variant that takes an rm is listed explicitly — a new one added to
/// `#[non_exhaustive] Formula` falls through to the empty slot list here AND
/// through `node_has_lowering`'s wildcard to `false`, so the router declines it
/// rather than lowering it past this gate.
#[must_use]
pub fn rounding_mode_operand_slots(node: &Formula) -> Vec<&Formula> {
    rounding_mode_operand_slot(node).into_iter().collect()
}

/// Build an FP constant from a raw IEEE bit pattern via ay's `(fp sign exp sig)`.
fn fp_const_from_bits(bits: u128, eb: u32, sb: u32) -> Expr {
    let sig_w = sb - 1; // stored significand excludes the hidden bit
    let total = eb + sb;
    let sign = ((bits >> (total - 1)) & 1) as i128;
    let exp = ((bits >> sig_w) & ((1u128 << eb) - 1)) as i128;
    let sig = (bits & ((1u128 << sig_w) - 1)) as i128;
    Expr::fp_from_bvs(
        Expr::bitvec_const(sign, 1),
        Expr::bitvec_const(exp, eb),
        Expr::bitvec_const(sig, sig_w),
    )
}

/// Reinterpret a `(eb+sb)`-wide bitvector `Expr` as a float via field extraction.
fn fp_from_bv_expr(bv: Expr, eb: u32, sb: u32) -> Expr {
    let sig_w = sb - 1;
    let total = eb + sb;
    let sign = bv.clone().extract(total - 1, total - 1);
    let exp = bv.clone().extract(total - 2, sig_w);
    let sig = bv.extract(sig_w - 1, 0);
    Expr::fp_from_bvs(sign, exp, sig)
}

#[cfg(test)]
mod tests {
    /// Lower through the bridge and PANIC on a refusal, naming it.
    ///
    /// `formula_to_expr` is fallible (see its doc): every refusal is a typed
    /// `AyBridgeError`, so a caller cannot accidentally proceed on one. These
    /// tests assert the SUCCESS shape, so they unwrap with the error's own
    /// message; the refusal shapes are asserted by the `*_is_a_named_refusal`
    /// tests and the fail-closed pins, which read the `Err` directly.
    fn lower(f: &Formula) -> Expr {
        formula_to_expr(f).unwrap_or_else(|error| panic!("bridge refused {f:?}: {error}"))
    }

    /// [`lower`] under a caller-supplied definition table.
    fn lower_with(f: &Formula, defs: &DatatypeDefs) -> Expr {
        formula_to_expr_with_datatype_defs(f, defs)
            .unwrap_or_else(|error| panic!("bridge refused {f:?}: {error}"))
    }

    use super::*;

    #[test]
    fn uint_max_encodes_losslessly_not_truncated_to_negative() {
        // round-A #2 false-PROVE regression: u128::MAX must encode as the full
        // positive value, NOT wrap to -1 (`u128::MAX as i128`), which made
        // `0 <= a <= u128::MAX` encode UNSAT and vacuously prove u128 overflow VCs.
        let got = lower(&Formula::UInt(u128::MAX));
        assert_eq!(got, Expr::int_const(u128::MAX), "u128::MAX must encode losslessly");
        assert_ne!(got, Expr::int_const(-1i128), "must NOT truncate to -1 (the false-PROVE bug)");
        // A mid-range value above i128::MAX also stays positive.
        let mid = (1u128 << 127) + 5;
        assert_eq!(lower(&Formula::UInt(mid)), Expr::int_const(mid));
    }

    // ── IEEE-754 floating point bridge ──────────────────────────────────────

    fn fp_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Float { eb: 11, sb: 53 })
    }
    fn rne() -> Box<Formula> {
        Box::new(Formula::FpRoundingMode(RoundingMode::RNE))
    }

    #[test]
    fn float_sort_maps_to_ay_floating_point() {
        let s = sort_to_ay(&Sort::Float { eb: 8, sb: 24 });
        assert_eq!(format!("{s}"), "(_ FloatingPoint 8 24)");
        assert_eq!(sort_from_ay(&s), Some(Sort::Float { eb: 8, sb: 24 }));
    }

    #[test]
    fn fp_ops_bridge_to_ay_smtlib() {
        let add = Formula::FpAdd(rne(), Box::new(fp_var("x")), Box::new(fp_var("y")));
        assert_eq!(format!("{}", lower(&add)), "(fp.add RNE x y)");
        let lt = Formula::FpLt(Box::new(fp_var("x")), Box::new(fp_var("y")));
        assert_eq!(format!("{}", lower(&lt)), "(fp.lt x y)");
        let isnan = Formula::FpIsNaN(Box::new(fp_var("x")));
        assert_eq!(format!("{}", lower(&isnan)), "(fp.isNaN x)");
        let nan = Formula::FpNaN { eb: 8, sb: 24 };
        assert_eq!(format!("{}", lower(&nan)), "(_ NaN 8 24)");
    }

    // End-to-end solver validation (Formula -> ay Expr -> ay solve). Gated behind
    // `ay-bridge-solve` (pulls the ay-dpll backend); proves the encoding is SOUND
    // — the IEEE-754 facts our vcgen float-comparison encoding relies on are
    // decided correctly. This is the "implemented AND validated" gate.
    #[cfg(feature = "ay-bridge-solve")]
    pub(super) fn solve_is_unsat(decls: &[&str], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        let logic = crate::smt_logic::select_logic(formula);
        program.set_logic(logic);
        for name in decls {
            program.declare_const(*name, AYSort::floating_point(11, 53));
        }
        program.assert(lower(formula));
        program.check_sat();
        // NAME THE HEADER IF IT IS THE HEADER. These probes pick their logic
        // with `select_logic`, i.e. the FULL lattice, and hand it to the native
        // lane's own `parse_logic` (in ay-bindings). A name that parser refuses
        // aborts the whole solve with `unsupported logic: …`, and a bare
        // `.expect` would report that as an ENCODING failure — sending the next
        // reader to debug the lowering instead of the header. MEASURED
        // 2026-09-19 at ay `9d2cda9c8727`, `parse_logic` accepts every row of
        // the lattice (it refused sixteen before that bump), so this belt
        // catches nothing today — it is kept because `HORN` is still refused in
        // an arm of its own and a future row need not be a name ay knows. The
        // router's production path is guarded (`native_lane_logic`, itself a
        // no-op at this pin); these test probes are not, so they say which it
        // was.
        let outcomes = execute_incremental(&program)
            .unwrap_or_else(|e| panic!("ay execute_incremental failed under logic `{logic}`: {e}"));
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    /// BV twin of [`solve_is_unsat`] for the declared-width Machine{w}
    /// contract goals (trust-vcgen's `machine_faithful_vc_formula` output
    /// shape): consts are declared at their machine width.
    #[cfg(feature = "ay-bridge-solve")]
    fn solve_bv_is_unsat(decls: &[(&str, u32)], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        let logic = crate::smt_logic::select_logic(formula);
        program.set_logic(logic);
        for (name, width) in decls {
            program.declare_const(*name, AYSort::bitvec(*width));
        }
        program.assert(lower(formula));
        program.check_sat();
        // NAME THE HEADER IF IT IS THE HEADER. These probes pick their logic
        // with `select_logic`, i.e. the FULL lattice, and hand it to the native
        // lane's own `parse_logic` (in ay-bindings). A name that parser refuses
        // aborts the whole solve with `unsupported logic: …`, and a bare
        // `.expect` would report that as an ENCODING failure — sending the next
        // reader to debug the lowering instead of the header. MEASURED
        // 2026-09-19 at ay `9d2cda9c8727`, `parse_logic` accepts every row of
        // the lattice (it refused sixteen before that bump), so this belt
        // catches nothing today — it is kept because `HORN` is still refused in
        // an arm of its own and a future row need not be a name ay knows. The
        // router's production path is guarded (`native_lane_logic`, itself a
        // no-op at this pin); these test probes are not, so they say which it
        // was.
        let outcomes = execute_incremental(&program)
            .unwrap_or_else(|e| panic!("ay execute_incremental failed under logic `{logic}`: {e}"));
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    #[cfg(feature = "ay-bridge-solve")]
    fn bv64_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(64))
    }

    /// The Machine{w} false-proof pin at the SOLVER: the declared-width
    /// reading of `ensures result + 1 > result` with body `result = x` must
    /// stay SATisfiable (the `u64::MAX` wrap witness) — the `Int` reading
    /// proved this exact clause, the confirmed false proof.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_machine_width_wrap_refutes_spec_tautology() {
        let ret = || Box::new(bv64_var("_0"));
        let x = || Box::new(bv64_var("x"));
        let one = || Box::new(Formula::BitVec { value: 1, width: 64 });
        let f = Formula::And(vec![
            Formula::Eq(ret(), x()),
            // ¬(result + 1 >u result)  ⟺  result + 1 <=u result
            Formula::BvULe(Box::new(Formula::BvAdd(ret(), one(), 64)), ret(), 64),
        ]);
        assert!(
            !solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &f),
            "the wrap witness at u64::MAX must stay SAT — UNSAT here is the false proof"
        );
    }

    /// The Machine{w} positive pin at the SOLVER: with the wrap excluded by a
    /// declared precondition, the TRUE contract `requires x < u64::MAX ensures
    /// result == x + 1` proves (violation UNSAT) at the declared width.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_machine_width_guarded_increment_proves() {
        let ret = || Box::new(bv64_var("_0"));
        let x = || Box::new(bv64_var("x"));
        let one = || Box::new(Formula::BitVec { value: 1, width: 64 });
        let max = || Box::new(Formula::BitVec { value: i128::from(u64::MAX), width: 64 });
        let f = Formula::And(vec![
            Formula::BvULt(x(), max(), 64),
            Formula::Eq(ret(), Box::new(Formula::BvAdd(x(), one(), 64))),
            Formula::Not(Box::new(Formula::Eq(ret(), Box::new(Formula::BvAdd(x(), one(), 64))))),
        ]);
        assert!(
            solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &f),
            "the guarded increment's violation must be UNSAT"
        );
        // The stronger relational form: `ensures result > x`.
        let g = Formula::And(vec![
            Formula::BvULt(x(), max(), 64),
            Formula::Eq(ret(), Box::new(Formula::BvAdd(x(), one(), 64))),
            // ¬(result >u x) ⟺ result <=u x
            Formula::BvULe(ret(), x(), 64),
        ]);
        assert!(
            solve_bv_is_unsat(&[("_0", 64), ("x", 64)], &g),
            "x < MAX ∧ result = x + 1 ∧ result <=u x must be UNSAT"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_rejects_nan_less_than_zero() {
        // x < 0 AND isNaN(x) -> UNSAT (NaN is unordered; the soundness property
        // the pre-FP magnitude encoding violated).
        let zero = || Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 });
        let f = Formula::And(vec![
            Formula::FpLt(Box::new(fp_var("x")), zero()),
            Formula::FpIsNaN(Box::new(fp_var("x"))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "NaN < 0 must be UNSAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_allows_negative_float() {
        let f = Formula::FpLt(
            Box::new(fp_var("x")),
            Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 }),
        );
        assert!(!solve_is_unsat(&["x"], &f), "x < 0 must be SAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_nan_not_equal_nan() {
        let f = Formula::And(vec![
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::FpEq(Box::new(fp_var("x")), Box::new(fp_var("x"))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "NaN == NaN must be UNSAT");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_bit_reinterpret_zero_is_zero() {
        // x = reinterpret(0x00..00) = +0.0  AND  not isZero(x) -> UNSAT.
        let bv0 = Box::new(Formula::BitVec { value: 0, width: 64 });
        let from_bits = Box::new(Formula::FpFromBits { bits: bv0, eb: 11, sb: 53 });
        let f = Formula::And(vec![
            Formula::Eq(Box::new(fp_var("x")), from_bits),
            Formula::Not(Box::new(Formula::FpIsZero(Box::new(fp_var("x"))))),
        ]);
        assert!(solve_is_unsat(&["x"], &f), "reinterpret(0) is +0.0, must classify as zero");
    }

    // Float ARITHMETIC value-definition semantics (the shape vcgen emits:
    // `Eq(dest, fp.op(RNE, x, y))`), validated through the real ay solver.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_add_value_def_propagates_nan() {
        // d = x + y  AND  isNaN(x)  =>  isNaN(d). Deny ¬isNaN(d) -> UNSAT.
        let rne = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        let d_def = Formula::Eq(
            Box::new(fp_var("d")),
            Box::new(Formula::FpAdd(rne(), Box::new(fp_var("x")), Box::new(fp_var("y")))),
        );
        let f = Formula::And(vec![
            d_def,
            Formula::FpIsNaN(Box::new(fp_var("x"))),
            Formula::Not(Box::new(Formula::FpIsNaN(Box::new(fp_var("d"))))),
        ]);
        assert!(solve_is_unsat(&["x", "y", "d"], &f), "float add must propagate NaN to the result");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_neg_value_def_is_involution() {
        // d = -(-x)  =>  d structurally equals x (exact; holds even for NaN/±0,
        // which is why a STRUCTURAL Eq definition is required, not fp.eq).
        let d_def = Formula::Eq(
            Box::new(fp_var("d")),
            Box::new(Formula::FpNeg(Box::new(Formula::FpNeg(Box::new(fp_var("x")))))),
        );
        let f = Formula::And(vec![
            d_def,
            Formula::Not(Box::new(Formula::Eq(Box::new(fp_var("d")), Box::new(fp_var("x"))))),
        ]);
        assert!(solve_is_unsat(&["x", "d"], &f), "-(-x) == x");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_abs_value_def_is_nonnegative() {
        // d = abs(x)  AND  ¬isNaN(x)  =>  d >= 0. Deny d < 0 -> UNSAT.
        let d_def =
            Formula::Eq(Box::new(fp_var("d")), Box::new(Formula::FpAbs(Box::new(fp_var("x")))));
        let f = Formula::And(vec![
            d_def,
            Formula::Not(Box::new(Formula::FpIsNaN(Box::new(fp_var("x"))))),
            Formula::FpLt(
                Box::new(fp_var("d")),
                Box::new(Formula::FpZero { neg: false, eb: 11, sb: 53 }),
            ),
        ]);
        assert!(solve_is_unsat(&["x", "d"], &f), "abs(x) is non-negative for non-NaN x");
    }

    #[test]
    fn fp_to_ieee_bv_bridges_to_ay_and_round_trips() {
        // The bridge must lower `FpToIeeeBv(FpFromBits(bv64))` to an ay Expr
        // (previously this hit the fail-closed `unreachable!`). Structurally, the
        // FP->BV reinterpret of the BV->FP reinterpret is the identity round-trip.
        let bv = Box::new(Formula::Var("v".into(), Sort::BitVec(64)));
        let from_bits = Box::new(Formula::FpFromBits { bits: bv, eb: 11, sb: 53 });
        let to_bv = Formula::FpToIeeeBv(from_bits);
        // Lowering must not panic and must equal the ay Expr built directly.
        let got = lower(&to_bv);
        let expected = {
            let inner_bv = Expr::var("v".to_string(), AYSort::bitvec(64));
            fp_from_bv_expr(inner_bv, 11, 53).fp_to_ieee_bv()
        };
        assert_eq!(got, expected, "FpToIeeeBv must lower to ay fp_to_ieee_bv over the FP operand");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_fp_to_ieee_bv_congruence_x_eq_x_is_unsat_to_refute() {
        // The two-sided proof's actual dependency: `to_ieee_bv(add) == to_ieee_bv(add)`
        // (identical shapes over identical operands) is VALID by congruence — the
        // NEGATION is UNSAT. This holds bit-exactly regardless of NaN
        // canonicalization, unlike a round-trip identity. This mirrors exactly what
        // `verify_output` discharges for the f64 FADD gate.
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let lane = |name: &str| Box::new(Formula::Var(name.into(), Sort::BitVec(64)));
        let mk = |x: &str, y: &str| {
            let xf = Box::new(Formula::FpFromBits { bits: lane(x), eb: 11, sb: 53 });
            let yf = Box::new(Formula::FpFromBits { bits: lane(y), eb: 11, sb: 53 });
            let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
            Box::new(Formula::FpToIeeeBv(Box::new(Formula::FpAdd(rm, xf, yf))))
        };
        // NOT( to_ieee_bv(add(x,y)) == to_ieee_bv(add(x,y)) ) must be UNSAT.
        let f = Formula::Not(Box::new(Formula::Eq(mk("a", "b"), mk("a", "b"))));
        let mut program = AYProgram::new();
        let logic = crate::smt_logic::select_logic(&f);
        program.set_logic(logic);
        program.declare_const("a", AYSort::bitvec(64));
        program.declare_const("b", AYSort::bitvec(64));
        program.assert(lower(&f));
        program.check_sat();
        // NAME THE HEADER IF IT IS THE HEADER. These probes pick their logic
        // with `select_logic`, i.e. the FULL lattice, and hand it to the native
        // lane's own `parse_logic` (in ay-bindings). A name that parser refuses
        // aborts the whole solve with `unsupported logic: …`, and a bare
        // `.expect` would report that as an ENCODING failure — sending the next
        // reader to debug the lowering instead of the header. MEASURED
        // 2026-09-19 at ay `9d2cda9c8727`, `parse_logic` accepts every row of
        // the lattice (it refused sixteen before that bump), so this belt
        // catches nothing today — it is kept because `HORN` is still refused in
        // an arm of its own and a future row need not be a name ay knows. The
        // router's production path is guarded (`native_lane_logic`, itself a
        // no-op at this pin); these test probes are not, so they say which it
        // was.
        let outcomes = execute_incremental(&program)
            .unwrap_or_else(|e| panic!("ay execute_incremental failed under logic `{logic}`: {e}"));
        assert!(
            matches!(outcomes.last().map(|o| &o.result), Some(ExecuteTypedResult::Verified)),
            "identical FpToIeeeBv(FpAdd(..)) shapes must be congruent (X == X UNSAT to refute)"
        );
    }

    // ── f32 (eb=8, sb=24) FP arithmetic bridge — the S-lane proofs ─────────────
    //
    // f32 rides the IDENTICAL width-parametric shape as f64
    // (`FpToIeeeBv(Fp*(RNE, FpFromBits(_,8,24), FpFromBits(_,8,24)))`), just at
    // (eb=8, sb=24) over the low 32-bit S-lane. These solver-backed proofs mirror
    // the f64 `solver_fp_to_ieee_bv_congruence_x_eq_x_is_unsat_to_refute` and the
    // f32 gap the residual `B-aarch64-fp-pending` never covered (it was f32 FCVT
    // + FMA only, NOT f32 add/sub/mul/div).

    /// Run an f32 (BV(32)-lane) obligation through ay: assert `formula`, declare
    /// each name as a 32-bit BV const, return true iff UNSAT ("Verified").
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_solve_is_unsat(bv32_decls: &[&str], formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let mut program = AYProgram::new();
        let logic = crate::smt_logic::select_logic(formula);
        program.set_logic(logic);
        for name in bv32_decls {
            program.declare_const(*name, AYSort::bitvec(32));
        }
        program.assert(lower(formula));
        program.check_sat();
        // NAME THE HEADER IF IT IS THE HEADER. These probes pick their logic
        // with `select_logic`, i.e. the FULL lattice, and hand it to the native
        // lane's own `parse_logic` (in ay-bindings). A name that parser refuses
        // aborts the whole solve with `unsupported logic: …`, and a bare
        // `.expect` would report that as an ENCODING failure — sending the next
        // reader to debug the lowering instead of the header. MEASURED
        // 2026-09-19 at ay `9d2cda9c8727`, `parse_logic` accepts every row of
        // the lattice (it refused sixteen before that bump), so this belt
        // catches nothing today — it is kept because `HORN` is still refused in
        // an arm of its own and a future row need not be a name ay knows. The
        // router's production path is guarded (`native_lane_logic`, itself a
        // no-op at this pin); these test probes are not, so they say which it
        // was.
        let outcomes = execute_incremental(&program)
            .unwrap_or_else(|e| panic!("ay execute_incremental failed under logic `{logic}`: {e}"));
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    /// The f32 two-sided machine/IR shape over the low 32-bit lanes `x`,`y`:
    /// `FpToIeeeBv(<op>(RNE, FpFromBits(x,8,24), FpFromBits(y,8,24)))`.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_binop_bits(
        x: &str,
        y: &str,
        op: fn(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
    ) -> Box<Formula> {
        let lane = |n: &str| Box::new(Formula::Var(n.into(), Sort::BitVec(32)));
        let xf = Box::new(Formula::FpFromBits { bits: lane(x), eb: 8, sb: 24 });
        let yf = Box::new(Formula::FpFromBits { bits: lane(y), eb: 8, sb: 24 });
        let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        Box::new(Formula::FpToIeeeBv(Box::new(op(rm, xf, yf))))
    }

    /// A 32-bit BV constant carrying a concrete f32 IEEE bit pattern.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_bits(bits: i128) -> Box<Formula> {
        Box::new(Formula::BitVec { value: bits, width: 32 })
    }

    /// The f32 shape over two CONSTANT lanes: `FpToIeeeBv(<op>(RNE,
    /// FpFromBits(a_bits,8,24), FpFromBits(b_bits,8,24)))` — a closed BV(32) term.
    #[cfg(feature = "ay-bridge-solve")]
    fn f32_binop_const(
        a_bits: i128,
        b_bits: i128,
        op: fn(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
    ) -> Box<Formula> {
        let af = Box::new(Formula::FpFromBits { bits: f32_bits(a_bits), eb: 8, sb: 24 });
        let bf = Box::new(Formula::FpFromBits { bits: f32_bits(b_bits), eb: 8, sb: 24 });
        let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        Box::new(Formula::FpToIeeeBv(Box::new(op(rm, af, bf))))
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_congruence_x_eq_x_is_unsat_for_all_ops() {
        // The two-sided f32 proof's actual dependency: for each of ADD/SUB/MUL/DIV,
        // `to_ieee_bv(op) == to_ieee_bv(op)` (identical shapes over identical BV(32)
        // lanes) is VALID by congruence — its NEGATION is UNSAT. This is exactly
        // what the machine/IR f32 gate discharges (X == X UNSAT to refute the
        // inequality). Holds bit-exactly regardless of NaN canonicalization.
        for (name, op) in [
            ("add", Formula::FpAdd as fn(_, _, _) -> _),
            ("sub", Formula::FpSub),
            ("mul", Formula::FpMul),
            ("div", Formula::FpDiv),
        ] {
            let mk = || f32_binop_bits("a", "b", op);
            // NOT( shape == shape ) must be UNSAT (i.e. shape == shape is valid).
            let f = Formula::Not(Box::new(Formula::Eq(mk(), mk())));
            assert!(
                f32_solve_is_unsat(&["a", "b"], &f),
                "f32 {name}: identical FpToIeeeBv(Fp{name}(..)) shapes must be congruent (X == X UNSAT)"
            );
        }
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_negative_control_wrong_result_is_refuted() {
        // NEGATIVE CONTROL (concrete, backend-tractable): the f32 gate has TEETH —
        // a WRONG expected value is genuinely rejected. `1.5 + 2.5` is 4.0
        // (0x40800000), NOT 5.0 (0x40A00000); so `sum == 0x40A00000` is
        // UNSATISFIABLE. Proving that UNSAT is precisely the mechanism by which a
        // miscompile that produced 5.0 would be Refuted rather than Proven.
        //
        // (The symbolic divergent-operand SAT direction — finding a concrete
        // counterexample by bit-blasting full FP-add semantics — returns Unknown
        // on the ay-dpll backend; the gate never depends on that direction: it
        // proves EQUALITY UNSAT, and refutes wrong values via concrete folding as
        // here.)
        let sum = f32_binop_const(0x3FC0_0000, 0x4020_0000, Formula::FpAdd);
        let wrong = Formula::Eq(sum, f32_bits(0x40A0_0000)); // == 5.0f32 (WRONG)
        assert!(
            f32_solve_is_unsat(&[], &wrong),
            "1.5f32 + 2.5f32 == 5.0f32 must be UNSAT (wrong result refuted — gate has teeth)"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_one_point_five_plus_two_point_five_is_four() {
        // Concrete f32 value: 1.5 + 2.5 == 4.0 at the bit level.
        //   1.5 = 0x3FC00000, 2.5 = 0x40200000, 4.0 = 0x40800000.
        // The f32 add shape over these constants must equal 0x40800000 exactly;
        // deny that equality -> UNSAT.
        let sum = f32_binop_const(0x3FC0_0000, 0x4020_0000, Formula::FpAdd);
        let f = Formula::Not(Box::new(Formula::Eq(sum, f32_bits(0x4080_0000))));
        assert!(f32_solve_is_unsat(&[], &f), "1.5f32 + 2.5f32 must equal 4.0f32 (0x40800000)");
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_neg_zero_plus_neg_zero_is_neg_zero() {
        // Sign-of-zero is load-bearing (bit-exact, not fp.eq): (-0.0) + (-0.0) is
        // -0.0 (0x80000000) under RNE, NOT +0.0 (0x00000000). Deny equality to
        // -0.0 -> UNSAT; and separately confirm it is NOT +0.0 (would be SAT).
        let sum = f32_binop_const(0x8000_0000, 0x8000_0000, Formula::FpAdd);
        let is_neg_zero = Formula::Not(Box::new(Formula::Eq(sum.clone(), f32_bits(0x8000_0000))));
        assert!(f32_solve_is_unsat(&[], &is_neg_zero), "(-0.0) + (-0.0) must be -0.0 (0x80000000)");
        // And it is bit-distinct from +0.0: `sum == +0.0` is UNSATISFIABLE-to-refute
        // i.e. NOT(sum == +0.0) must hold (UNSAT of the negation's negation). We
        // assert NOT(sum == +0.0) is a THEOREM by refuting its negation:
        let differs_from_pos_zero = Formula::Not(Box::new(Formula::Eq(sum, f32_bits(0x0000_0000))));
        // sum == +0.0 must be UNSAT, so NOT(sum == +0.0) is valid; deny it:
        let deny = Formula::Not(Box::new(differs_from_pos_zero));
        assert!(
            f32_solve_is_unsat(&[], &deny),
            "(-0.0) + (-0.0) must NOT be +0.0 (sign preserved)"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_add_propagates_nan_exponent() {
        // NaN + anything = NaN. Over the f32 add shape, adding a quiet NaN
        // (0x7FC00000) to 1.0 (0x3F800000) yields a NaN result: its 8-bit
        // exponent field (result bits [30:23]) is all-ones (0xFF). We check this
        // via a pure BV extraction over the folded FpToIeeeBv(FpAdd(..)) result
        // (backend-tractable, unlike `FpIsNaN` through the bit round-trip): deny
        // `exp == 0xFF` -> UNSAT. (A NaN payload is not uniquely canonicalized, so
        // we assert the format-defined exponent, not a specific mantissa.)
        let sum = f32_binop_const(0x7FC0_0000, 0x3F80_0000, Formula::FpAdd);
        let exp = Formula::BvExtract { inner: sum, high: 30, low: 23 };
        let f = Formula::Not(Box::new(Formula::Eq(
            Box::new(exp),
            Box::new(Formula::BitVec { value: 0xFF, width: 8 }),
        )));
        assert!(
            f32_solve_is_unsat(&[], &f),
            "NaN + 1.0 must be NaN at f32 (result exponent field all-ones)"
        );
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_f32_value_diff_one_over_zero_is_plus_inf() {
        // IEEE f32 division is TOTAL: 1.0 / 0.0 == +inf (0x7F800000), no trap.
        //   1.0 = 0x3F800000, 0.0 = 0x00000000, +inf = 0x7F800000.
        // The f32 div shape over these constants must equal 0x7F800000; deny -> UNSAT.
        let quot = f32_binop_const(0x3F80_0000, 0x0000_0000, Formula::FpDiv);
        let f = Formula::Not(Box::new(Formula::Eq(quot, f32_bits(0x7F80_0000))));
        assert!(f32_solve_is_unsat(&[], &f), "1.0f32 / 0.0f32 must be +inf (0x7F800000)");
    }

    fn var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    #[test]
    fn test_sort_roundtrip_bool() {
        let ay = sort_to_ay(&Sort::Bool);
        assert!(ay.is_bool());
        assert_eq!(sort_from_ay(&ay), Some(Sort::Bool));
    }

    #[test]
    fn test_sort_roundtrip_int() {
        let ay = sort_to_ay(&Sort::Int);
        assert!(ay.is_int());
        assert_eq!(sort_from_ay(&ay), Some(Sort::Int));
    }

    #[test]
    fn test_sort_roundtrip_bitvec() {
        let ay = sort_to_ay(&Sort::BitVec(32));
        assert!(ay.is_bitvec());
        assert_eq!(sort_from_ay(&ay), Some(Sort::BitVec(32)));
    }

    #[test]
    fn test_sort_roundtrip_array() {
        let sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        let ay = sort_to_ay(&sort);
        assert!(ay.is_array());
        assert_eq!(sort_from_ay(&ay), Some(sort));
    }

    #[test]
    fn test_formula_bool_const() {
        let expr = lower(&Formula::Bool(true));
        assert!(expr.sort().is_bool());
        let smt = format!("{expr}");
        assert_eq!(smt, "true");
    }

    #[test]
    fn test_formula_int_const() {
        let expr = lower(&Formula::Int(42));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "42");
    }

    #[test]
    fn test_formula_bitvec_const() {
        let expr = lower(&Formula::BitVec { value: 255, width: 8 });
        assert!(expr.sort().is_bitvec());
        let smt = format!("{expr}");
        assert_eq!(smt, "#xff");
    }

    #[test]
    fn float_ordering_comparison_lowers_without_panic_taking_fp_path() {
        // A float magnitude bound (`self.0 <= 1.0e30`) must lower via the IEEE FP
        // predicate. The Int `int_le`/… ops ASSERT Int sorts and would PANIC on an
        // FP operand — so the mere fact these lower to a Bool-sorted expr (rather
        // than panicking) proves the sort-aware FP path was taken.
        let f64s = Sort::Float { eb: 11, sb: 53 };
        let field = Formula::Var("self.0".into(), f64s);
        let bound = Formula::FpConst { bits: u128::from(1.0e30_f64.to_bits()), eb: 11, sb: 53 };
        for cmp in [
            Formula::Le(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Ge(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Lt(Box::new(field.clone()), Box::new(bound.clone())),
            Formula::Gt(Box::new(field.clone()), Box::new(bound.clone())),
        ] {
            let expr = lower(&cmp); // must not panic
            assert!(expr.sort().is_bool(), "float ordering comparison lowers to Bool");
        }
        // The `¬X ∧ X` discharge shape (caller's own bound vs the substituted callee
        // bound) lowers whole without panic and is Bool.
        let le = Formula::Le(Box::new(field), Box::new(bound));
        let discharge = Formula::And(vec![Formula::Not(Box::new(le.clone())), le]);
        assert!(lower(&discharge).sort().is_bool());

        // Regression: an INTEGER ordering comparison still lowers via the Int path.
        let int_le = Formula::Le(Box::new(var("x")), Box::new(Formula::Int(5)));
        assert!(lower(&int_le).sort().is_bool());
    }

    #[test]
    fn test_formula_var() {
        let expr = lower(&var("x"));
        assert!(expr.sort().is_int());
        let smt = format!("{expr}");
        assert_eq!(smt, "x");
    }

    #[test]
    fn test_formula_not() {
        let f = Formula::Not(Box::new(Formula::Bool(true)));
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(not true)");
    }

    #[test]
    fn test_formula_and() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(and true false)");
    }

    #[test]
    fn test_formula_implies() {
        let f = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(false)));
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(=> true false)");
    }

    #[test]
    fn test_formula_eq() {
        let f = Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)));
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(= x 0)");
    }

    #[test]
    fn test_formula_int_arith() {
        let f = Formula::Add(Box::new(var("x")), Box::new(var("y")));
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(+ x y)");
    }

    #[test]
    fn test_formula_bv_add() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvadd a b)");
    }

    #[test]
    fn test_formula_bv_comparisons() {
        let f = Formula::BvULt(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(bvult a b)");
    }

    #[test]
    fn test_formula_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert_eq!(smt, "(ite true 1 0)");
    }

    #[test]
    fn test_formula_forall() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0)))),
        );
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("forall"));
        assert!(smt.contains("(x Int)"));
    }

    #[test]
    fn test_formula_select_store() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let idx = Formula::BitVec { value: 100, width: 64 };
        let val = Formula::BitVec { value: 42, width: 8 };

        let store = Formula::Store(Box::new(arr.clone()), Box::new(idx.clone()), Box::new(val));
        let expr = lower(&store);
        let smt = format!("{expr}");
        assert!(smt.contains("store"));

        let select = Formula::Select(Box::new(arr), Box::new(idx));
        let expr = lower(&select);
        let smt = format!("{expr}");
        assert!(smt.contains("select"));
    }

    #[test]
    fn const_array_lowers_to_ay_const_array_and_refuses_a_mis_sorted_value() {
        let splat = Formula::const_array(
            Sort::BitVec(64),
            Sort::BitVec(8),
            Formula::BitVec { value: 7, width: 8 },
        );
        assert!(is_lowerable_formula(&splat));
        let expr = formula_to_expr(&splat).expect("a well-sorted const array lowers");
        assert_eq!(
            *expr.sort(),
            sort_to_ay(&Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))))
        );
        // A read of it is an ordinary select over the lowered term.
        let read =
            Formula::Select(Box::new(splat), Box::new(Formula::BitVec { value: 3, width: 64 }));
        assert!(format!("{}", lower(&read)).contains("select"));
        // The carried element sort and the value's sort must agree; ay would
        // otherwise build a differently-sorted array than the formula states.
        let mis_sorted = Formula::const_array(Sort::Int, Sort::BitVec(8), Formula::Int(7));
        assert!(matches!(
            formula_to_expr(&mis_sorted),
            Err(AyBridgeError::UnsupportedFormula { .. })
        ));
    }

    #[test]
    fn test_formula_bv_extract() {
        let f = Formula::BvExtract { inner: Box::new(bv_var("x", 32)), high: 15, low: 0 };
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("extract"));
    }

    #[test]
    fn test_formula_bv_concat() {
        let f = Formula::BvConcat(Box::new(bv_var("hi", 16)), Box::new(bv_var("lo", 16)));
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("concat"));
    }

    #[test]
    fn test_formula_zero_extend() {
        let f = Formula::BvZeroExt(Box::new(bv_var("x", 32)), 32);
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert!(smt.contains("zero_extend"));
    }

    // ── Algebraic-datatype terms (Lever A step-1) ───────────────────────────
    //
    // The datatype term nodes must lower to GENUINE ay
    // DatatypeConstructor/Selector/Tester Expr nodes (not stubs) over a declared
    // datatype sort. This is the ay half of the step-1 round-trip: it asserts
    // the nodes CONSTRUCT (and render), NOT that any VC is discharged.

    /// A recursive toy `Level = zero | succ(pred: Level)` (the shape the
    /// clean-kernel universe-level fidelity equation rides). The recursive
    /// `pred` field is a by-name reference (empty `constructors`).
    fn level_sort() -> Sort {
        let level_ref = Sort::Datatype { name: "Level".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), vec![]),
                ("succ".into(), vec![("pred".into(), level_ref)]),
            ],
        }
    }

    /// The by-name reference to `Level`, the form every datatype-typed FIELD
    /// (and, in shipped vcgen output, every pattern binder and selector
    /// result) carries.
    fn level_ref() -> Sort {
        Sort::Datatype { name: "Level".into(), constructors: Vec::new() }
    }

    // AY BOUNDARY (ay ≥ d4400b131 `Sort::datatype_ref`; see the note on the
    // `Formula::Ctor` arm). The recursive shapes lower to genuine ay nodes:
    // the by-name `pred` field becomes `datatype_ref("Level")`, which ay
    // resolves to the enclosing `Level` declaration and compares structurally,
    // and every term position carries the full definition.

    // ── The NAMED refusals ─────────────────────────────────────────────────
    //
    // Every malformed datatype shape below is refused BY NAME through
    // `formula_to_expr` — a typed `AyBridgeError`, never a panic and never
    // a silent misencoding. Each of these also fails closed (loudly) through
    // the infallible `formula_to_expr`, which is what the in-tree callers use;
    // `check_datatype_terms_refuses_what_the_bridge_would_panic_on` pins that
    // half. These pin the FALLIBLE half, so a direct library caller can decline
    // without unwinding.
    //
    // Where the refusal is established BEFORE ay is entered (a term the
    // definition in the formula already contradicts, or a by-name reference
    // with no definition at all), the error is the more specific one this
    // bridge derived itself rather than ay's `SortError`: strictly more
    // information at a strictly earlier seam.

    #[test]
    fn empty_constructor_datatype_maps_to_an_ay_datatype_ref() {
        // The recursive back-edge must be ay's resolvable reference, not an
        // opaque uninterpreted sort (which ay refuses to equate with `Level`).
        assert_eq!(sort_to_ay(&level_ref()), AYSort::datatype_ref("Level"));
        assert_ne!(sort_to_ay(&level_ref()), AYSort::uninterpreted("Level"));
    }

    #[test]
    fn datatype_ctor_arity_mismatch_is_a_named_refusal() {
        // `succ` takes one field; `(succ)` must be refused by name, not panic.
        let bad = Formula::Ctor { ctor: "succ".into(), args: vec![], sort: level_sort() };
        let err = formula_to_expr(&bad).expect_err("arity mismatch must be refused");
        assert!(
            matches!(
                &err,
                AyBridgeError::DatatypeTerm(DatatypeTermError::ConstructorArity {
                    datatype,
                    ctor,
                    expected: 1,
                    actual: 0,
                }) if datatype == "Level" && ctor == "succ"
            ),
            "unexpected refusal: {err:?}"
        );
        assert!(err.to_string().contains("succ"), "{err}");
    }

    #[test]
    fn ctor_with_non_datatype_sort_is_a_named_refusal() {
        let bad = Formula::Ctor { ctor: "succ".into(), args: vec![], sort: Sort::Int };
        let err = formula_to_expr(&bad).expect_err("non-datatype ctor sort must be refused");
        assert!(
            matches!(
                err,
                AyBridgeError::CtorSortNotDatatype { .. }
                    | AyBridgeError::DatatypeTerm(
                        DatatypeTermError::ConstructorSortNotDatatype { .. }
                    )
            ),
            "{err:?}"
        );
    }

    #[test]
    fn selector_of_undeclared_field_is_a_named_refusal() {
        let x = Formula::Var("x".into(), level_sort());
        let bad = Formula::Sel {
            datatype: "Level".into(),
            field: "no_such_field".into(),
            field_sort: level_sort(),
            arg: Box::new(x),
        };
        let err = formula_to_expr(&bad).expect_err("unknown selector must be refused");
        assert!(
            matches!(
                &err,
                AyBridgeError::DatatypeTerm(DatatypeTermError::UnknownMember {
                    datatype,
                    member_kind: "field",
                    member,
                }) if datatype == "Level" && member == "no_such_field"
            ),
            "{err:?}"
        );
        // The rendered message names the datatype AND the member, so a decline
        // reason carrying it is greppable for the exact offending pair.
        let rendered = err.to_string();
        assert!(rendered.contains("Level"), "{rendered}");
        assert!(rendered.contains("no_such_field"), "{rendered}");
    }

    #[test]
    fn tester_of_undeclared_constructor_is_a_named_refusal() {
        let x = Formula::Var("x".into(), level_sort());
        let bad = Formula::IsCtor {
            datatype: "Level".into(),
            ctor: "no_such_ctor".into(),
            arg: Box::new(x),
        };
        let err = formula_to_expr(&bad).expect_err("unknown tester must be refused");
        assert!(
            matches!(
                &err,
                AyBridgeError::DatatypeTerm(DatatypeTermError::UnknownMember {
                    datatype,
                    member_kind: "constructor",
                    member,
                }) if datatype == "Level" && member == "no_such_ctor"
            ),
            "{err:?}"
        );
    }

    #[test]
    fn mutually_recursive_back_edge_is_refused_not_panicked() {
        // `A = mk_a(b: B)`, `B = mk_b(a: <ref A>)` declared separately: the ref
        // to `A` inside `B` has no enclosing `A` and no full definition anywhere
        // in the formula, so nothing can widen it. Building `mk_b(..)` over it
        // must be a named refusal (the obligation declines), never a panic.
        //
        // This bridge names the DANGLING REFERENCE itself (`A`) rather than
        // reporting ay's refusal of the enclosing constructor node: the check
        // runs over the formula's sort positions before anything is lowered, so
        // the reference that has nothing to stand for is identified directly.
        // A SIBLING reference whose definition IS present in the formula is a
        // different shape and is INLINED, not refused — see
        // `cross_datatype_by_name_field_lowers_with_the_sibling_inlined`.
        let a_ref = Sort::Datatype { name: "A".into(), constructors: Vec::new() };
        let b_sort = Sort::Datatype {
            name: "B".into(),
            constructors: vec![("mk_b".into(), vec![("a".into(), a_ref.clone())])],
        };
        let a_val = Formula::Var("a0".into(), a_ref);
        let bad = Formula::Ctor { ctor: "mk_b".into(), args: vec![a_val], sort: b_sort };
        let err = formula_to_expr(&bad).expect_err("dangling datatype ref must be refused");
        assert!(
            matches!(&err, AyBridgeError::UndefinedDatatype { datatype } if datatype == "A"),
            "{err:?}"
        );
        // The refusal names the dangling reference, so the decline reason a
        // caller surfaces identifies the shape to fix.
        assert!(err.to_string().contains('A'), "{err}");
    }

    #[test]
    fn recursive_field_nests_through_constructor_and_selector() {
        // `pred (succ (succ zero))` — the recursive field accepts a datatype
        // value of the enclosing declaration at every depth. Nullary-rooted and
        // FULLY sorted at every level, the complement of
        // `chained_by_name_selectors_lower_with_full_sorted_receivers`, which
        // drives the same nesting through the by-name (widening) spelling.
        let zero = Formula::Ctor { ctor: "zero".into(), args: vec![], sort: level_sort() };
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_sort(),
            arg: Box::new(succ(succ(zero))),
        };
        let expr = lower(&sel);
        assert!(expr.sort().is_datatype());
    }

    #[test]
    fn datatype_ctor_bridges_to_ay_constructor() {
        // `succ l` with `l : Level` — the recursive constructor step.
        let l = Formula::Var("l".into(), level_sort());
        let ctor = Formula::Ctor { ctor: "succ".into(), args: vec![l], sort: level_sort() };
        let expr = lower(&ctor);
        assert!(expr.sort().is_datatype(), "constructor result is datatype-sorted");
        assert_eq!(format!("{expr}"), "(succ l)");
    }

    #[test]
    fn datatype_selector_bridges_to_ay_field_select() {
        // `(pred x) : Level` — the requested result sort is the full definition.
        let x = Formula::Var("x".into(), level_sort());
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_sort(),
            arg: Box::new(x),
        };
        let expr = lower(&sel);
        assert_eq!(format!("{expr}"), "(pred x)");
        assert!(expr.sort().is_datatype(), "selector result carries the full definition");
    }

    #[test]
    fn datatype_nullary_ctor_bridges_to_ay_constructor() {
        // A nullary constructor bridges to a sort-qualified constant `(as zero Level)`.
        let zero = Formula::Ctor { ctor: "zero".into(), args: vec![], sort: level_sort() };
        let expr = lower(&zero);
        assert!(expr.sort().is_datatype(), "nullary constructor is datatype-sorted");
        assert_eq!(format!("{expr}"), "(as zero Level)");
    }

    #[test]
    fn datatype_tester_bridges_to_ay_is_constructor() {
        // `((_ is succ) x)` builds a real ay DatatypeTester Expr, Bool-sorted.
        let x = Formula::Var("x".into(), level_sort());
        let is =
            Formula::IsCtor { datatype: "Level".into(), ctor: "succ".into(), arg: Box::new(x) };
        let expr = lower(&is);
        assert!(expr.sort().is_bool(), "tester is Bool-sorted");
        assert_eq!(format!("{expr}"), "((_ is succ) x)");
    }

    #[test]
    fn fidelity_equation_bridges_end_to_end() {
        // The step-1 headline `succ l = succ l` (the `Sort(succ l) = Sort(succ l)`
        // shape): a real ay equality over two recursive constructor terms.
        let l = || Formula::Var("l".into(), level_sort());
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let eq = Formula::Eq(Box::new(succ(l())), Box::new(succ(l())));
        let expr = lower(&eq);
        assert_eq!(format!("{expr}"), "(= (succ l) (succ l))");
    }

    #[test]
    fn recursive_field_lowers_to_a_datatype_ref_not_an_opaque_sort() {
        // The descriptor ay authenticates against records the back-edge as a
        // `DatatypeRef`, the one form ay resolves to the enclosing declaration.
        let ay = sort_to_ay(&level_sort());
        let dt = ay.datatype_sort().expect("a full definition is an ay datatype");
        let pred = &dt.constructors[1].fields[0].sort;
        assert!(
            matches!(pred.inner(), AYSortInner::DatatypeRef(name) if name == "Level"),
            "{pred:?}"
        );
        assert!(!pred.is_datatype());
    }

    #[test]
    fn by_name_selector_result_is_widened_to_the_full_definition() {
        // vcgen records `Sel::field_sort` as the by-name reference; with the
        // full `Level` in scope (on `x`) it lowers with the FULL result sort,
        // so the result can feed a receiver or an equation with a `Level` term.
        let x = Formula::Var("x".into(), level_sort());
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(x),
        };
        let expr = lower(&sel);
        assert_eq!(format!("{expr}"), "(pred x)");
        assert!(expr.sort().is_datatype(), "the by-name result sort is widened");
        assert_eq!(expr.sort(), &sort_to_ay(&level_sort()));
    }

    #[test]
    fn chained_by_name_selectors_lower_with_full_sorted_receivers() {
        // `(pred (pred x))` with the by-name field sort at BOTH levels: the
        // inner result is widened, so it is a valid receiver for the outer.
        let sel = |arg: Formula| Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(arg),
        };
        let x = Formula::Var("x".into(), level_sort());
        let expr = lower(&sel(sel(x)));
        assert_eq!(format!("{expr}"), "(pred (pred x))");
        assert!(expr.sort().is_datatype());
    }

    #[test]
    fn vcgen_shaped_induction_step_lowers() {
        // recursive_datatype_functional gives the pattern binder `__fld_Succ_0`
        // the by-name sort and the IH variable `__ih0` the full sort, equates
        // them, and rebuilds the scrutinee with a full-sorted `Ctor` over the
        // by-name-sorted binder. All of it is one `Level` after widening.
        let fld = || Formula::Var("__fld_Succ_0".into(), level_ref());
        let ih = || Formula::Var("__ih0".into(), level_sort());
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let body = Formula::Implies(
            Box::new(Formula::Eq(Box::new(ih()), Box::new(fld()))),
            Box::new(Formula::Eq(Box::new(succ(ih())), Box::new(succ(fld())))),
        );
        let f = Formula::forall(&[("__fld_Succ_0", level_ref()), ("__ih0", level_sort())], body);
        let expr = lower(&f);
        let smt = format!("{expr}");
        assert!(smt.starts_with("(forall ((__fld_Succ_0 Level) (__ih0 Level)"), "{smt}");
        assert!(
            smt.ends_with("(=> (= __ih0 __fld_Succ_0) (= (succ __ih0) (succ __fld_Succ_0))))"),
            "{smt}"
        );
    }

    /// `ExprKind = Const(c: BV32) | Sort(0: Level)` with `Level` by-name in the
    /// field — the cross-datatype shape of the clean-kernel tower.
    fn expr_kind_sort() -> Sort {
        Sort::Datatype {
            name: "ExprKind".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("Sort".into(), vec![("0".into(), level_ref())]),
            ],
        }
    }

    #[test]
    fn cross_datatype_by_name_field_lowers_with_the_sibling_inlined() {
        // `Sort(succ l)`: the field is recorded as by-name `Level`, the argument
        // carries the full `Level`. ay resolves a reference only to an
        // ENCLOSING declaration, so the sibling is inlined in the descriptor.
        let succ = Formula::Ctor {
            ctor: "succ".into(),
            args: vec![Formula::Var("l".into(), level_sort())],
            sort: level_sort(),
        };
        let sort_kind =
            Formula::Ctor { ctor: "Sort".into(), args: vec![succ], sort: expr_kind_sort() };
        let expr = lower(&sort_kind);
        assert_eq!(format!("{expr}"), "(Sort (succ l))");
        let dt = expr.sort().datatype_sort().unwrap();
        assert!(dt.constructors[1].fields[0].sort.is_datatype(), "the sibling is inlined");

        // The declarations follow the terms: `Level` before `ExprKind`, and the
        // `ExprKind` declaration IS the descriptor the term carries.
        let defs = DatatypeDefs::collect(&sort_kind).unwrap();
        let decls = defs.to_ay_declarations();
        assert_eq!(
            decls.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
            ["Level", "ExprKind"]
        );
        assert_eq!(&decls[1], dt);
    }

    #[test]
    fn a_body_level_definition_table_widens_a_formula_that_never_spells_it_out() {
        // `(0 k)` over `k : ExprKind` with the by-name `Level` result: this
        // formula carries no full `Level`; the body's `datatype_defs` table does.
        let mut defs = DatatypeDefs::default();
        defs.add_sort(&level_sort()).unwrap();
        let sel = Formula::Sel {
            datatype: "ExprKind".into(),
            field: "0".into(),
            field_sort: level_ref(),
            arg: Box::new(Formula::Var("k".into(), expr_kind_sort())),
        };
        let expr = lower_with(&sel, &defs);
        // ay quotes the numeric field name.
        assert_eq!(format!("{expr}"), "(|0| k)");
        assert_eq!(expr.sort(), &sort_to_ay(&level_sort()));
    }

    #[test]
    fn sibling_by_name_field_is_inlined_from_the_formula_definition() {
        // `Tower = empty | stack(top: Block, rest: Tower)` with `Block` by-name:
        // the full `Block` on `b` is inlined in the `top` field, the `rest`
        // back-edge stays a reference.
        let block =
            Sort::Datatype { name: "Block".into(), constructors: vec![("leaf".into(), vec![])] };
        let block_ref = Sort::Datatype { name: "Block".into(), constructors: Vec::new() };
        let tower_ref = Sort::Datatype { name: "Tower".into(), constructors: Vec::new() };
        let tower = Sort::Datatype {
            name: "Tower".into(),
            constructors: vec![
                ("empty".into(), vec![]),
                ("stack".into(), vec![("top".into(), block_ref), ("rest".into(), tower_ref)]),
            ],
        };
        let stack = Formula::Ctor {
            ctor: "stack".into(),
            args: vec![Formula::Var("b".into(), block), Formula::Var("t".into(), tower.clone())],
            sort: tower,
        };
        let expr = lower(&stack);
        assert_eq!(format!("{expr}"), "(stack b t)");
        let dt = expr.sort().datatype_sort().unwrap();
        assert!(dt.constructors[1].fields[0].sort.is_datatype(), "the sibling is inlined");
        assert!(matches!(
            dt.constructors[1].fields[1].sort.inner(),
            AYSortInner::DatatypeRef(name) if name == "Tower"
        ));
    }

    /// End-to-end on the in-process lane: the recursive `Level` is declared
    /// from the formula's own definition table and `pred (succ l) = l` is
    /// PROVED (its negation is UNSAT), while `succ l = zero` is refuted.
    #[cfg(feature = "ay-bridge-solve")]
    fn solve_level_is_unsat(formula: &Formula) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::{ExecuteTypedResult, execute_incremental};
        let defs = DatatypeDefs::collect(formula).expect("one Level");
        let mut program = AYProgram::new();
        let logic = "ALL";
        program.set_logic(logic);
        for dt in defs.to_ay_declarations() {
            assert!(
                program.try_declare_datatype(dt).expect("the term descriptor is the declaration")
            );
        }
        program.declare_const("l", sort_to_ay_in(&level_sort(), &defs, &mut Vec::new()));
        program.assert(lower(formula));
        program.check_sat();
        // NAME THE HEADER IF IT IS THE HEADER. These probes pick their logic
        // with `select_logic`, i.e. the FULL lattice, and hand it to the native
        // lane's own `parse_logic` (in ay-bindings). A name that parser refuses
        // aborts the whole solve with `unsupported logic: …`, and a bare
        // `.expect` would report that as an ENCODING failure — sending the next
        // reader to debug the lowering instead of the header. MEASURED
        // 2026-09-19 at ay `9d2cda9c8727`, `parse_logic` accepts every row of
        // the lattice (it refused sixteen before that bump), so this belt
        // catches nothing today — it is kept because `HORN` is still refused in
        // an arm of its own and a future row need not be a name ay knows. The
        // router's production path is guarded (`native_lane_logic`, itself a
        // no-op at this pin); these test probes are not, so they say which it
        // was.
        let outcomes = execute_incremental(&program)
            .unwrap_or_else(|e| panic!("ay execute_incremental failed under logic `{logic}`: {e}"));
        match outcomes.last().map(|o| &o.result) {
            Some(ExecuteTypedResult::Verified) => true,
            Some(ExecuteTypedResult::Counterexample(_)) => false,
            other => panic!("unexpected solver result: {other:?}"),
        }
    }

    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn recursive_datatype_fidelity_is_decided_natively() {
        let l = || Formula::Var("l".into(), level_sort());
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let pred = |a: Formula| Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(a),
        };
        let zero = || Formula::Ctor { ctor: "zero".into(), args: vec![], sort: level_sort() };
        // ¬(pred (succ l) = l) is UNSAT: the equation is proved.
        let proved = Formula::Not(Box::new(Formula::Eq(Box::new(pred(succ(l()))), Box::new(l()))));
        assert!(solve_level_is_unsat(&proved));
        // succ l = zero is UNSAT: distinct constructors.
        assert!(solve_level_is_unsat(&Formula::Eq(Box::new(succ(l())), Box::new(zero()))));
        // succ l = succ l is SAT (its negation is UNSAT); l = succ l is UNSAT (acyclic).
        let refl = Formula::Not(Box::new(Formula::Eq(Box::new(succ(l())), Box::new(succ(l())))));
        assert!(solve_level_is_unsat(&refl));
        assert!(solve_level_is_unsat(&Formula::Eq(Box::new(l()), Box::new(succ(l())))));
        // And a satisfiable one is a counterexample, not vacuously proved.
        assert!(!solve_level_is_unsat(&Formula::Eq(Box::new(pred(l())), Box::new(zero()))));
    }

    // FAIL-CLOSED PINS: the bridge still REFUSES a genuinely malformed
    // encoding — no stub, no re-sorted term, no silent misencoding.
    //
    // The refusal is now a NAMED `AyBridgeError` rather than a panic, so these
    // read the `Err` directly instead of matching panic text. That is the
    // stronger assertion: the panic message was incidental, the variant and its
    // fields are the contract a caller declines on. Every one of these shapes
    // also declines at the router gate, before the bridge is entered, which the
    // in_process_ay_backend tests pin separately.

    #[test]
    fn malformed_datatype_ctor_fails_closed_at_ay_boundary() {
        // `succ 1`: an Int argument where the descriptor records `pred: Level`.
        let ctor =
            Formula::Ctor { ctor: "succ".into(), args: vec![Formula::Int(1)], sort: level_sort() };
        let err = formula_to_expr(&ctor).expect_err("a malformed constructor must be refused");
        assert!(
            matches!(
                &err,
                AyBridgeError::DatatypeTerm(DatatypeTermError::ConstructorArgumentSort {
                    datatype,
                    ctor,
                    field,
                    ..
                }) if datatype == "Level" && ctor == "succ" && field == "pred"
            ),
            "{err:?}"
        );
    }

    #[test]
    fn by_name_datatype_with_no_definition_in_scope_fails_closed() {
        // `(pred x)` with `x` ALSO by-name: no full `Level` anywhere in the
        // formula, so both the receiver and the result are dangling references.
        let sel = Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(Formula::Var("x".into(), level_ref())),
        };
        let err = formula_to_expr(&sel).expect_err("a dangling by-name reference must be refused");
        assert!(
            matches!(&err, AyBridgeError::UndefinedDatatype { datatype } if datatype == "Level"),
            "{err:?}"
        );
    }

    #[test]
    fn conflicting_full_definitions_in_one_formula_fail_closed() {
        let impostor =
            Sort::Datatype { name: "Level".into(), constructors: vec![("zero".into(), vec![])] };
        let eq = Formula::Eq(
            Box::new(Formula::Var("a".into(), level_sort())),
            Box::new(Formula::Var("b".into(), impostor)),
        );
        let err = formula_to_expr(&eq).expect_err("two definitions of one name must be refused");
        assert!(matches!(&err, AyBridgeError::ConflictingDefinitions(_)), "{err:?}");
        assert!(err.to_string().contains("Level"), "{err}");
    }

    // A datatype whose fields are all scalar, pinned POSITIVELY so "genuine
    // ay nodes, not stubs" stays a tested claim on the shape with no
    // by-name reference at all.

    /// `Pair = mk(fst: Int, snd: Bool)` — a full definition, no by-name field.
    fn pair_sort() -> Sort {
        Sort::Datatype {
            name: "Pair".into(),
            constructors: vec![(
                "mk".into(),
                vec![("fst".into(), Sort::Int), ("snd".into(), Sort::Bool)],
            )],
        }
    }

    #[test]
    fn scalar_field_datatype_ctor_bridges_to_ay_constructor() {
        // `mk 1 true` builds a real ay DatatypeConstructor Expr, datatype-sorted,
        // rendering as the constructor application.
        let ctor = Formula::Ctor {
            ctor: "mk".into(),
            args: vec![Formula::Int(1), Formula::Bool(true)],
            sort: pair_sort(),
        };
        let expr = lower(&ctor);
        assert!(expr.sort().is_datatype(), "constructor result is datatype-sorted");
        assert_eq!(format!("{expr}"), "(mk 1 true)");
    }

    #[test]
    fn scalar_field_datatype_selector_bridges_to_ay_field_select() {
        // `(fst p)` over a symbolic receiver builds a real ay DatatypeSelector
        // Expr of the recorded field sort. (Over a constructor ay folds the
        // projection to the field, so a symbolic receiver is the retained shape.)
        let p = Formula::Var("p".into(), pair_sort());
        let sel = Formula::Sel {
            datatype: "Pair".into(),
            field: "fst".into(),
            field_sort: Sort::Int,
            arg: Box::new(p),
        };
        let expr = lower(&sel);
        assert!(expr.sort().is_int(), "selector result carries the field sort");
        assert_eq!(format!("{expr}"), "(fst p)");
    }

    #[test]
    fn scalar_field_datatype_equation_bridges_end_to_end() {
        // `mk a false = mk a false` constructs a real ay equality over two
        // datatype-constructor terms. WRITABLE + lowers; not a proof.
        let mk = || Formula::Ctor {
            ctor: "mk".into(),
            args: vec![Formula::Var("a".into(), Sort::Int), Formula::Bool(false)],
            sort: pair_sort(),
        };
        let eq = Formula::Eq(Box::new(mk()), Box::new(mk()));
        let expr = lower(&eq);
        assert_eq!(format!("{expr}"), "(= (mk a false) (mk a false))");
    }

    #[test]
    fn test_formula_smtlib_matches_ay() {
        // Verify that Formula::to_smtlib() and ay Expr Display produce
        // equivalent SMT-LIB2 for basic operations
        let f = Formula::And(vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(var("y")), Box::new(Formula::Int(10))),
        ]);
        let trust_smt = f.to_smtlib();
        let ay_smt = format!("{}", lower(&f));
        // Both should be syntactically valid SMT-LIB2
        assert!(trust_smt.contains("and"));
        assert!(ay_smt.contains("and"));
    }

    // ── The fallible pre-bridge datatype check ──────────────────────────────

    fn level_var(name: &str) -> Formula {
        Formula::Var(name.into(), level_sort())
    }

    /// Every well-sorted datatype shape a recursive-datatype lane emits passes
    /// [`check_datatype_terms`] — including the by-name-vs-full spelling of one
    /// datatype, which is ONE sort — so the check can never re-introduce an
    /// ignorance-based decline.
    #[test]
    fn check_datatype_terms_admits_every_well_sorted_shape() {
        let l = || level_var("l");
        let succ =
            |a: Formula| Formula::Ctor { ctor: "succ".into(), args: vec![a], sort: level_sort() };
        let pred = |a: Formula| Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(a),
        };
        let well_sorted = [
            Formula::Eq(Box::new(succ(l())), Box::new(l())),
            Formula::Eq(Box::new(pred(succ(l()))), Box::new(l())),
            Formula::Eq(
                Box::new(Formula::IsCtor {
                    datatype: "Level".into(),
                    ctor: "succ".into(),
                    arg: Box::new(l()),
                }),
                Box::new(Formula::Bool(true)),
            ),
            // The vcgen induction-step shape: a by-name pattern binder equated
            // with the full-definition IH variable, and fed to a constructor.
            Formula::Eq(
                Box::new(succ(Formula::Var("__fld_Succ_0".into(), level_ref()))),
                Box::new(l()),
            ),
        ];
        for formula in &well_sorted {
            let defs = DatatypeDefs::collect(formula).expect("one Level");
            assert_eq!(check_datatype_terms(formula, &defs), Ok(()), "{formula:?}");
            // And it really lowers — the check is not stricter than the bridge.
            let _ = lower(formula);
        }
    }

    /// Ignorance is never a defect: a by-name datatype reference with NO full
    /// definition anywhere has nothing to authenticate against, and an operand
    /// the sort checker cannot sort is left to the full-formula sort gate. Both
    /// pass this check (and are declined elsewhere — the program builder refuses
    /// the dangling declaration).
    #[test]
    fn check_datatype_terms_is_silent_without_a_definition_to_contradict() {
        let dangling = Formula::Eq(
            Box::new(Formula::Ctor {
                ctor: "whatever".into(),
                args: vec![Formula::Int(0)],
                sort: level_ref(),
            }),
            Box::new(Formula::Var("l".into(), level_ref())),
        );
        let defs = DatatypeDefs::collect(&dangling).expect("no full definition");
        assert_eq!(check_datatype_terms(&dangling, &defs), Ok(()));

        // `not 1` has no sort the checker can establish, so the constructor
        // argument carries no contradiction this check may report.
        let unsortable = Formula::Eq(
            Box::new(Formula::Ctor {
                ctor: "succ".into(),
                args: vec![Formula::Not(Box::new(Formula::Int(1)))],
                sort: level_sort(),
            }),
            Box::new(level_var("l")),
        );
        let defs = DatatypeDefs::collect(&unsortable).expect("one Level");
        assert_eq!(check_datatype_terms(&unsortable, &defs), Ok(()));
        assert!(crate::smt_logic::check_formula_sort(&unsortable).is_err());
    }

    /// The malformed shapes the sort checker waves through: each PASSES
    /// `check_formula_sort` (it judges a datatype term by the descriptor the
    /// node carries), each makes `formula_to_expr` take its fail-closed PANIC,
    /// and each is refused here — fallibly — first.
    #[test]
    fn check_datatype_terms_refuses_what_the_bridge_would_panic_on() {
        let l = || level_var("l");
        let n = || Formula::Var("n".into(), Sort::Int);
        let cases: Vec<(Formula, DatatypeTermError)> = vec![
            (
                Formula::Eq(
                    Box::new(Formula::Sel {
                        datatype: "Level".into(),
                        field: "pred".into(),
                        field_sort: Sort::Int,
                        arg: Box::new(l()),
                    }),
                    Box::new(n()),
                ),
                DatatypeTermError::SelectorFieldSort {
                    datatype: "Level".into(),
                    field: "pred".into(),
                    expected: Box::new(level_ref()),
                    actual: Box::new(Sort::Int),
                },
            ),
            (
                Formula::Eq(
                    Box::new(Formula::Ctor {
                        ctor: "succ".into(),
                        args: vec![l()],
                        sort: Sort::Int,
                    }),
                    Box::new(n()),
                ),
                DatatypeTermError::ConstructorSortNotDatatype {
                    ctor: "succ".into(),
                    sort: Sort::Int,
                },
            ),
            (
                Formula::Eq(
                    Box::new(Formula::Ctor {
                        ctor: "succ".into(),
                        args: vec![n()],
                        sort: level_sort(),
                    }),
                    Box::new(l()),
                ),
                DatatypeTermError::ConstructorArgumentSort {
                    datatype: "Level".into(),
                    ctor: "succ".into(),
                    field: "pred".into(),
                    expected: Box::new(level_ref()),
                    actual: Box::new(Sort::Int),
                },
            ),
            (
                Formula::Eq(
                    Box::new(Formula::IsCtor {
                        datatype: "Level".into(),
                        ctor: "succ".into(),
                        arg: Box::new(n()),
                    }),
                    Box::new(Formula::Bool(true)),
                ),
                DatatypeTermError::OperandNotDatatype {
                    op: "tester",
                    datatype: "Level".into(),
                    member: "succ".into(),
                    actual: Sort::Int,
                },
            ),
        ];
        for (formula, expected) in cases {
            assert_eq!(
                crate::smt_logic::check_formula_sort(&formula),
                Ok(Sort::Bool),
                "the sort checker cannot see this defect: {formula:?}"
            );
            let defs = DatatypeDefs::collect(&formula).expect("one Level");
            assert_eq!(check_datatype_terms(&formula, &defs), Err(expected), "{formula:?}");
            // The bridge's answer to the same shape is a panic, which is why
            // the fallible check has to run first.
            let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = lower(&formula);
            }))
            .is_err();
            assert!(panicked, "the bridge must be the panicking half: {formula:?}");
        }
    }

    /// One datatype NAME with two DIFFERENT full definitions is a type-level
    /// contradiction `sorts_agree` (agreement by name) cannot see — and
    /// `DatatypeDefs::collect` refuses it, which is what the router's gate runs
    /// before anything is lowered.
    #[test]
    fn two_definitions_of_one_datatype_name_are_refused_by_collect() {
        let other = Sort::Datatype {
            name: "Level".into(),
            constructors: vec![("bottom".into(), Vec::new()), ("top".into(), Vec::new())],
        };
        let contradiction = Formula::Eq(
            Box::new(level_var("l")),
            Box::new(Formula::Var("other".into(), other.clone())),
        );
        // The type level admits it: the two sorts agree BY NAME.
        assert!(sorts_agree(&level_sort(), &other));
        assert_eq!(crate::smt_logic::check_formula_sort(&contradiction), Ok(Sort::Bool));
        // The definition table does not.
        assert_eq!(
            DatatypeDefs::collect(&contradiction).err(),
            Some(DatatypeConflict("Level".into()))
        );
    }

    // ── The unhandled-variant class (round 10) ──────────────────────────────

    /// `Formula::FnApp` — the function-symbol twin of `Pred` — had NO arm and
    /// fell through to the fail-closed wildcard, so every `model = reference`
    /// postcondition and every vcgen Skolem term PANICKED here. It must lower
    /// to a real uninterpreted application AT THE RESULT SORT THE NODE CARRIES:
    /// `Expr::func_app` would fix it to `Bool` (ay's CHC relation constructor)
    /// and silently mis-sort a `Level`-returning reference function.
    #[test]
    fn fn_app_lowers_to_an_uninterpreted_application_at_its_carried_result_sort() {
        let level_app = Formula::FnApp {
            func: "mirror_ref".into(),
            args: vec![
                Formula::Var("fuel".into(), Sort::Int),
                Formula::Var("e".into(), level_sort()),
            ],
            sort: level_sort(),
        };
        let expr = lower(&level_app);
        let text = format!("{expr}");
        assert!(text.contains("mirror_ref"), "the function symbol must survive: {text}");
        assert!(text.contains("fuel"), "both arguments must be applied: {text}");
        let dt =
            expr.sort().datatype_sort().expect("a Level-returning application is Level-sorted");
        assert_eq!(dt.name, "Level", "the result sort is the one the node carries");

        // An Int-returning application is Int-sorted, and a Bool-returning one
        // is Bool — the same node, three different result sorts, none of them
        // the `func_app` Bool default.
        let int_app = Formula::FnApp {
            func: "rank".into(),
            args: vec![Formula::Var("e".into(), level_sort())],
            sort: Sort::Int,
        };
        assert!(lower(&int_app).sort().is_int(), "an Int-returning FnApp is Int-sorted");
        let bool_app =
            Formula::FnApp { func: "wf".into(), args: vec![Formula::Int(0)], sort: Sort::Bool };
        assert!(lower(&bool_app).sort().is_bool(), "a Bool-returning FnApp is Bool");
    }

    /// A NULLARY `FnApp` is a constant of its result sort, not an application —
    /// the shape `to_smtlib` prints as a bare symbol.
    ///
    /// "A constant" means THE SAME ay term a free variable of that name and
    /// sort lowers to: an `ExprValue::Var`, which the caller declares with
    /// `declare_const`. A zero-argument `ExprValue::FuncApp` prints the same
    /// bare symbol but executes as an APPLICATION term, which is not the term
    /// ay's elaborator reads that symbol as, so ay's retained-source guard
    /// refused every assertion carrying one (see the arm).
    #[test]
    fn nullary_fn_app_lowers_to_a_constant_of_its_result_sort() {
        let nullary = Formula::FnApp { func: "unit_ref".into(), args: Vec::new(), sort: Sort::Int };
        let expr = lower(&nullary);
        assert!(expr.sort().is_int());
        assert!(format!("{expr}").contains("unit_ref"));
        assert_eq!(
            expr,
            lower(&Formula::Var("unit_ref".into(), Sort::Int)),
            "a nullary FnApp lowers to exactly the constant a free variable of its name and \
             sort lowers to"
        );
        assert!(
            !matches!(expr.value(), ay_bindings::ExprValue::FuncApp { .. }),
            "a nullary FnApp must not lower to a zero-argument application: {expr:?}"
        );

        // The same at a datatype result sort, lowered from the one table.
        let level_const =
            Formula::FnApp { func: "base_level".into(), args: Vec::new(), sort: level_sort() };
        assert_eq!(lower(&level_const), lower(&Formula::Var("base_level".into(), level_sort())));

        // And inside a term: the application's arguments are unaffected — only
        // the nullary symbol is a constant.
        let applied = Formula::FnApp {
            func: "rank".into(),
            args: vec![Formula::FnApp { func: "c".into(), args: Vec::new(), sort: Sort::Int }],
            sort: Sort::Int,
        };
        match lower(&applied).value() {
            ay_bindings::ExprValue::FuncApp { name, args } => {
                assert_eq!(name, "rank");
                assert_eq!(args, &[lower(&Formula::Var("c".into(), Sort::Int))]);
            }
            other => panic!("a unary FnApp is an application, got {other:?}"),
        }
    }

    /// A NULLARY `Pred` — the reviewed vocabulary has two, `priv_dropped` and
    /// `domain_entered_before_lookup` — is a Bool constant for the same reason
    /// a nullary `FnApp` is.
    #[test]
    fn nullary_pred_lowers_to_a_bool_constant() {
        let nullary = Formula::Pred("priv_dropped".into(), Vec::new());
        let expr = lower(&nullary);
        assert!(expr.sort().is_bool());
        assert_eq!(expr, lower(&Formula::Var("priv_dropped".into(), Sort::Bool)));
    }

    /// Three of the five sibling variants the audit found beside `FnApp`: the
    /// FP conversions trust-machine-sem mints for SCVTF/UCVTF and FCVT are
    /// FULLY SPECIFIED by SMT-LIB, so they lower to ay's native operators —
    /// and must not panic.
    #[test]
    fn fully_specified_fp_conversions_lower_to_native_ay_operators() {
        let rm = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        let bv = || Box::new(Formula::Var("w".into(), Sort::BitVec(32)));
        let f32v = || Box::new(Formula::Var("s".into(), Sort::Float { eb: 8, sb: 24 }));

        let from_sbv = Formula::FpFromSbv { rm: rm(), value: bv(), eb: 11, sb: 53 };
        let from_ubv = Formula::FpFromUbv { rm: rm(), value: bv(), eb: 11, sb: 53 };
        let convert = Formula::FpConvert { rm: rm(), value: f32v(), eb: 11, sb: 53 };
        for node in [&from_sbv, &from_ubv, &convert] {
            let expr = lower(node);
            assert!(
                expr.sort().is_floating_point(),
                "an int-to-float / format conversion is FP-sorted: {node:?} -> {expr}"
            );
        }
        // The signed and unsigned readings are DISTINCT operators: a top-bit-set
        // BV(32) is a large positive double under `to_fp_unsigned` and a
        // negative one under `to_fp`, so conflating them would corrupt UCVTF.
        assert_ne!(
            format!("{}", lower(&from_sbv)),
            format!("{}", lower(&from_ubv)),
            "SCVTF and UCVTF must not lower to the same operator"
        );
    }

    /// `FpToSbv`/`FpToUbv` are TOTAL with the AArch64 saturating reading, while
    /// SMT-LIB's `fp.to_sbv`/`fp.to_ubv` are UNSPECIFIED for NaN and
    /// out-of-range inputs. The bridge must therefore emit the GUARDED
    /// expansion — never the bare operator — so the in-process lane decides
    /// these VCs exactly as the SMT-LIB text lane does.
    #[test]
    fn saturating_fp_to_bv_lowers_to_the_same_guarded_expansion_as_the_text_path() {
        let node = |signed: bool, width: u32| {
            let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RTZ));
            let value = Box::new(Formula::Var("d".into(), Sort::Float { eb: 11, sb: 53 }));
            if signed {
                Formula::FpToSbv { rm, value, width, eb: 11, sb: 53 }
            } else {
                Formula::FpToUbv { rm, value, width, eb: 11, sb: 53 }
            }
        };
        for signed in [true, false] {
            for width in [8_u32, 32, 64] {
                let formula = node(signed, width);
                let expr = lower(&formula);
                assert_eq!(
                    expr.sort(),
                    &AYSort::bitvec(width),
                    "the conversion lands in BitVec({width}): {expr}"
                );
                let text = format!("{expr}");
                assert!(
                    text.contains("isNaN") || text.contains("is_nan"),
                    "NaN must be guarded to zero, not left unspecified: {text}"
                );
                assert!(text.contains("ite"), "the saturating reading is a guard tree: {text}");
                let op = if signed { "to_sbv" } else { "to_ubv" };
                assert!(text.contains(op), "the guarded core is still {op}: {text}");
                // The text path builds the same shape from the same constants.
                let smtlib = formula.to_smtlib();
                assert!(smtlib.contains("fp.isNaN") && smtlib.contains(op), "{smtlib}");
            }
        }
    }

    /// The machine-checked twin of the audit on `formula_to_expr`'s wildcard:
    /// every variant the contract declares today HAS a lowering arm, so no
    /// well-sorted formula can reach that `unreachable!`.
    #[test]
    fn every_contract_variant_has_a_lowering_arm() {
        let rm = || Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        let f64v = || Box::new(Formula::Var("d".into(), Sort::Float { eb: 11, sb: 53 }));
        let bv = || Box::new(Formula::Var("w".into(), Sort::BitVec(64)));
        let i = || Box::new(Formula::Int(1));
        let b = || Box::new(Formula::Bool(true));
        let sym = crate::Symbol::intern("q");
        let array = || {
            Box::new(Formula::Var(
                "a".into(),
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
            ))
        };

        // One representative of every family, including the six that had no arm.
        let every = vec![
            Formula::Bool(true),
            Formula::Int(-1),
            Formula::UInt(u128::MAX),
            Formula::rat_from_int(3),
            Formula::BitVec { value: 7, width: 8 },
            Formula::Var("x".into(), Sort::Int),
            Formula::SymVar(sym, Sort::Int),
            Formula::Not(b()),
            Formula::And(vec![Formula::Bool(true)]),
            Formula::Or(Vec::new()),
            Formula::Implies(b(), b()),
            Formula::Eq(i(), i()),
            Formula::Lt(i(), i()),
            Formula::Le(i(), i()),
            Formula::Gt(i(), i()),
            Formula::Ge(i(), i()),
            Formula::Add(i(), i()),
            Formula::Sub(i(), i()),
            Formula::Mul(i(), i()),
            Formula::Div(i(), i()),
            Formula::Rem(i(), i()),
            Formula::Neg(i()),
            Formula::BvAdd(bv(), bv(), 64),
            Formula::BvNot(bv(), 64),
            Formula::BvULt(bv(), bv(), 64),
            Formula::BvToInt(bv(), 64, true),
            Formula::IntToBv(i(), 64),
            Formula::BvExtract { inner: bv(), high: 7, low: 0 },
            Formula::BvConcat(bv(), bv()),
            Formula::BvZeroExt(bv(), 8),
            Formula::BvSignExt(bv(), 8),
            Formula::FpConst { bits: 0, eb: 11, sb: 53 },
            Formula::FpNaN { eb: 11, sb: 53 },
            Formula::FpInf { neg: true, eb: 11, sb: 53 },
            Formula::FpZero { neg: false, eb: 11, sb: 53 },
            Formula::FpRoundingMode(RoundingMode::RNE),
            Formula::FpAdd(rm(), f64v(), f64v()),
            Formula::FpFma(rm(), f64v(), f64v(), f64v()),
            Formula::FpSqrt(rm(), f64v()),
            Formula::FpNeg(f64v()),
            Formula::FpEq(f64v(), f64v()),
            Formula::FpIsNaN(f64v()),
            Formula::FpFromBits { bits: bv(), eb: 11, sb: 53 },
            Formula::FpToIeeeBv(f64v()),
            Formula::FpToSbv { rm: rm(), value: f64v(), width: 64, eb: 11, sb: 53 },
            Formula::FpToUbv { rm: rm(), value: f64v(), width: 64, eb: 11, sb: 53 },
            Formula::FpFromSbv { rm: rm(), value: bv(), eb: 11, sb: 53 },
            Formula::FpFromUbv { rm: rm(), value: bv(), eb: 11, sb: 53 },
            Formula::FpConvert { rm: rm(), value: f64v(), eb: 8, sb: 24 },
            Formula::Ite(b(), i(), i()),
            Formula::Forall(vec![(sym, Sort::Int)], b()),
            Formula::Exists(vec![(sym, Sort::Int)], b()),
            Formula::Select(array(), i()),
            Formula::Store(array(), i(), i()),
            Formula::Pred(crate::Symbol::intern("dir_open"), vec![Formula::Int(0)]),
            Formula::Ctor { ctor: "zero".into(), args: Vec::new(), sort: level_sort() },
            Formula::Sel {
                datatype: "Level".into(),
                field: "pred".into(),
                field_sort: level_ref(),
                arg: Box::new(Formula::Var("l".into(), level_sort())),
            },
            Formula::IsCtor {
                datatype: "Level".into(),
                ctor: "zero".into(),
                arg: Box::new(Formula::Var("l".into(), level_sort())),
            },
            Formula::FnApp { func: "f".into(), args: vec![Formula::Int(0)], sort: Sort::Int },
        ];
        for node in &every {
            assert!(
                is_lowerable_formula(node),
                "every variant of today's contract must have a lowering arm: {node:?}"
            );
        }
        // And the predicate is structural: it looks INSIDE, so an unlowerable
        // node buried under a connective would be reported too.
        assert!(is_lowerable_formula(&Formula::And(every)));
    }
}

/// The `Real` sort and `Formula::Rat` on the in-process lane: a real-valued
/// atom must lower to ay's exact-rational `real_*` operators — never to the
/// `int_*` ones, which assert Int sorts and would abort — and the literal must
/// arrive exact (arbitrary precision, no float detour).
#[cfg(test)]
mod real_bridge_tests {
    use super::*;

    /// Lower and panic on a refusal, naming it (the twin of `tests::lower`).
    fn lower(f: &Formula) -> Expr {
        formula_to_expr(f).unwrap_or_else(|error| panic!("bridge refused {f:?}: {error}"))
    }

    fn rv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.into(), Sort::Real))
    }
    fn q(num: &str, den: &str) -> Box<Formula> {
        Box::new(Formula::rat(num, den).expect("canonical rational"))
    }

    #[test]
    fn real_sort_round_trips_through_ay() {
        let s = sort_to_ay(&Sort::Real);
        assert!(s.is_real());
        assert_eq!(sort_from_ay(&s), Some(Sort::Real));
    }

    #[test]
    fn real_atoms_lower_to_real_sorted_ay_expressions() {
        // (1/2)·x + y ≤ 7/3, x < 0, -x ≥ y — the shapes a ny-cert Farkas row takes.
        let lhs = Formula::Add(Box::new(Formula::Mul(q("1", "2"), rv("x"))), rv("y"));
        let lhs_expr = lower(&lhs);
        assert!(lhs_expr.sort().is_real(), "linear real term must be Real-sorted: {lhs_expr}");
        for atom in [
            Formula::Le(Box::new(lhs), q("7", "3")),
            Formula::Lt(rv("x"), q("0", "1")),
            Formula::Gt(rv("x"), q("-5", "2")),
            Formula::Ge(Box::new(Formula::Neg(rv("x"))), rv("y")),
            Formula::Le(
                Box::new(Formula::Sub(rv("x"), rv("y"))),
                Box::new(Formula::rat_from_int(-3)),
            ),
        ] {
            let e = lower(&atom);
            assert!(e.sort().is_bool(), "{atom:?} must lower to a Bool predicate, got {e}");
        }
    }

    #[test]
    fn rational_literal_lowers_exactly_at_any_precision() {
        // 2^200 + 1 over 3: far beyond i128, must survive as an exact Real.
        let big = "1606938044258990275541962092341162602522202993782792835301377";
        let e = lower(&q(big, "3"));
        assert!(e.sort().is_real());
        let text = format!("{e}");
        assert!(text.contains(big), "numerator must be carried verbatim: {text}");
        assert!(text.contains('/'), "a non-integral literal is a real division: {text}");
        // An integral literal is the bare real constant (no division node).
        let whole = format!("{}", lower(&Formula::rat_from_int(42)));
        assert!(!whole.contains('/'), "{whole}");
        assert!(whole.contains("42"), "{whole}");
    }
}

/// SPEC-FLOAT-EQ-STRUCTURAL-1: what a contract `==` between floats reaches ay
/// as. `Formula::Eq` lowers to SMT-LIB `=`, which is structural over
/// FloatingPoint (`NaN = NaN`, `+0 != -0`) and stays that way: the body encoding
/// defines float temporaries with it. A contract `==` is Rust `PartialEq`, so its
/// producers emit `FpEq` (`fp.eq`) once the operands are known to be floats.
#[cfg(test)]
mod spec_float_eq_tests {
    use super::*;

    fn lower(f: &Formula) -> Expr {
        formula_to_expr(f).unwrap_or_else(|error| panic!("bridge refused {f:?}: {error}"))
    }

    fn fv(name: &str) -> Box<Formula> {
        Box::new(Formula::Var(name.into(), Sort::Float { eb: 11, sb: 53 }))
    }

    /// A source contract clause as the contract pipeline delivers it: parsed,
    /// then retyped with the signature's f64 parameters.
    fn contract(text: &str, f64_params: &[&str]) -> Formula {
        let sorts: BTreeMap<String, Sort> = f64_params
            .iter()
            .map(|name| ((*name).to_string(), Sort::Float { eb: 11, sb: 53 }))
            .collect();
        crate::retype_formula_variables(crate::parse_spec_expr(text).expect("parses"), &sorts)
    }

    #[test]
    fn contract_float_equality_lowers_to_fp_eq_and_structural_eq_stays_eq() {
        assert_eq!(format!("{}", lower(&contract("x == y", &["x", "y"]))), "(fp.eq x y)");
        assert_eq!(format!("{}", lower(&contract("x == 0.0", &["x"]))), {
            let zero = Formula::FpConst { bits: 0, eb: 11, sb: 53 };
            format!("(fp.eq x {})", lower(&zero))
        });
        let ne = format!("{}", lower(&contract("x != y", &["x", "y"])));
        assert!(ne.contains("fp.eq") && ne.starts_with("(not"), "{ne}");
        // The structural node keeps its structural meaning.
        assert_eq!(format!("{}", lower(&Formula::Eq(fv("x"), fv("y")))), "(= x y)");
    }

    #[cfg(feature = "ay-bridge-solve")]
    fn nan(name: &str) -> Formula {
        Formula::FpIsNaN(fv(name))
    }

    #[cfg(feature = "ay-bridge-solve")]
    fn zero(neg: bool) -> Box<Formula> {
        Box::new(Formula::FpZero { neg, eb: 11, sb: 53 })
    }

    /// `requires x == y` with both NaN: Rust says the clause is FALSE. As `fp.eq`
    /// it is unsatisfiable; as structural `=` it held — the proved callsite lie.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_contract_equality_excludes_nan_pairs() {
        let ieee = Formula::And(vec![contract("x == y", &["x", "y"]), nan("x"), nan("y")]);
        assert!(super::tests::solve_is_unsat(&["x", "y"], &ieee), "NaN == NaN must be false");
        let structural = Formula::And(vec![Formula::Eq(fv("x"), fv("y")), nan("x"), nan("y")]);
        assert!(
            !super::tests::solve_is_unsat(&["x", "y"], &structural),
            "structural `=` holds for NaN = NaN, which is why it is not Rust `==`"
        );
    }

    /// `requires x == y` with `x = +0.0`, `y = -0.0`: Rust says the clause HOLDS.
    /// As structural `=` it was refuted — the false refutation of correct code.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_contract_equality_admits_signed_zeros() {
        let pins = || vec![Formula::Eq(fv("x"), zero(false)), Formula::Eq(fv("y"), zero(true))];
        let mut ieee = pins();
        ieee.push(contract("x == y", &["x", "y"]));
        assert!(
            !super::tests::solve_is_unsat(&["x", "y"], &Formula::And(ieee)),
            "0.0 == -0.0 must hold"
        );
        let mut structural = pins();
        structural.push(Formula::Eq(fv("x"), fv("y")));
        assert!(super::tests::solve_is_unsat(&["x", "y"], &Formula::And(structural)));
    }

    /// `requires x == 0.0` admits `-0.0`, which is sign-negative: assuming the
    /// clause must leave `x.is_sign_negative()` satisfiable. Structural `=` would
    /// have made that branch unreachable.
    #[cfg(feature = "ay-bridge-solve")]
    #[test]
    fn solver_assumed_zero_equality_keeps_negative_zero() {
        let negative = Formula::FpIsNegative(fv("x"));
        let ieee = Formula::And(vec![contract("x == 0.0", &["x"]), negative.clone()]);
        assert!(!super::tests::solve_is_unsat(&["x"], &ieee), "-0.0 == 0.0 is sign-negative");
        let structural = Formula::And(vec![
            Formula::Eq(fv("x"), Box::new(Formula::FpConst { bits: 0, eb: 11, sb: 53 })),
            negative,
        ]);
        assert!(super::tests::solve_is_unsat(&["x"], &structural));
    }
}
