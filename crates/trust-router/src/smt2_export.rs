// trust-router/smt2_export.rs: SMT-LIB2 debug export format
//
// Provides --emit=smt2 functionality: exports VCs as standard SMT-LIB2 scripts
// for debugging and interop with any SMT-LIB2 compliant solver (`ay`, cvc5, etc.).
//
// Delegates formula/sort serialization to the canonical `to_smtlib()` methods
// in trust-types. This module adds VC-level structure: metadata comments,
// (set-logic), (declare-fun), (assert), (check-sat), and batch export.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeSet;

use trust_types::logic_lattice::Theories;
use trust_types::{Formula, Sort, escape_smtlib_symbol};

use crate::disjoint_components::uninterpreted_symbol_signatures;

/// Convert a formula to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Formula::to_smtlib()` in trust-types.
#[must_use]
pub(crate) fn formula_to_smt2(formula: &Formula) -> String {
    formula.to_smtlib()
}

/// Convert a sort to its SMT-LIB2 text representation.
///
/// Delegates to the canonical `Sort::to_smtlib()` in trust-types.
#[must_use]
pub(crate) fn sort_to_smt2(sort: &Sort) -> String {
    sort.to_smtlib()
}

/// Collect `(declare-fun ...)` declarations for all free variables in a formula.
///
/// Returns declarations sorted by variable name for deterministic output.
/// Quantifier-bound variables are excluded.
///
/// THREE SOURCES: [`emit_sort_preamble`] for the datatype sort identifiers,
/// [`collect_free_vars`] for the variables, and
/// [`uninterpreted_symbol_declarations`] for the `Pred`/`FnApp` symbols. Every
/// SMT-LIB emitter on the ROUTER'S VERIFICATION PATH composes the same three —
/// `in_process_ay_backend::problem_smt2`, `build_program` and
/// `smtlib_backend::generate_smtlib_script` — so none of them can declare a
/// different set from another.
///
/// TWO OTHER EMITTERS/COLLECTORS EXIST, and an earlier version of this comment
/// called these three sources "each of them the only one of its kind", which
/// was false. Both live in trust-types, both are OFF this path, and they are
/// listed here so the claim above stays the narrow one it can support:
///
/// * `trust_types::smt_logic::collect_free_var_decls` — the other free-variable
///   collector. It is no longer a SECOND traversal: it is now the one
///   scope-tracking implementation and [`collect_free_vars`] delegates to it
///   (see that function). Folding them together also fixed a real divergence —
///   it used to take every `Var`/`SymVar` node whose NAME was free somewhere,
///   so a name bound in one subterm and free in another yielded two
///   `(declare-fun …)` lines at two sorts.
/// * `trust_types::smt_printer::SmtPrinter::format_benchmark` — a second
///   complete `(set-logic)`/`(declare-fun)`/`(assert)`/`(check-sat)` emitter.
///   It is NOT folded in, deliberately, and the reason is precise: it is a
///   DEBUG PRETTY-PRINTER with no caller anywhere in `crates/*/src` (checked),
///   it takes its logic name as an `Option<&str>` PARAMETER rather than from
///   any selector, and it emits neither the datatype sort preamble nor the
///   `Pred`/`FnApp` signatures — so it cannot render a datatype-sorted or
///   uninterpreted-symbol query correctly and must never be used to build a
///   query a solver is asked to decide. Its own doc now says so. Giving it the
///   router's three sources would mean moving them into trust-types, which is
///   the wrong direction: the sort preamble and the signature map are facts
///   about the ROUTER's transcript contract.
/// * (A third DERIVED emitter, `trust_report::binary`'s
///   `collect_formula_sort_declarations`, formats `(declare-fun x () S)` lines
///   for the binary VC REPORT. It is a report field, never a solver input, and
///   it now shares the single collector above.)
#[must_use]
pub(crate) fn emit_declarations(formula: &Formula) -> Vec<String> {
    let mut decls = emit_sort_preamble(formula);

    decls.extend(collect_free_vars(formula).into_iter().map(|(name, sort)| {
        format!("(declare-fun {} () {})", escape_smtlib_symbol(&name), sort_to_smt2(&sort))
    }));

    decls.extend(uninterpreted_symbol_declarations(formula));

    decls
}

/// Append the exact lines of [`emit_declarations`], each followed by `'\n'`,
/// directly into `out` without allocating an intermediate `Vec<String>` or
/// per-signature `params: Vec<String>`.
#[cfg(any(feature = "ay-backend", test))]
pub(crate) fn write_declarations(formula: &Formula, out: &mut String) {
    use std::fmt::Write as _;

    for decl in emit_sort_preamble(formula) {
        out.push_str(&decl);
        out.push('\n');
    }
    for (name, sort) in collect_free_vars(formula) {
        let _ = writeln!(
            out,
            "(declare-fun {} () {})",
            escape_smtlib_symbol(&name),
            sort_to_smt2(&sort)
        );
    }
    for (name, (arg_sorts, result_sort)) in uninterpreted_symbol_signatures(formula) {
        out.push_str("(declare-fun ");
        out.push_str(&escape_smtlib_symbol(&name));
        out.push_str(" (");
        for (idx, arg_sort) in arg_sorts.iter().enumerate() {
            if idx != 0 {
                out.push(' ');
            }
            out.push_str(&sort_to_smt2(arg_sort));
        }
        out.push_str(") ");
        out.push_str(&sort_to_smt2(&result_sort));
        out.push_str(")\n");
    }
}

/// The SORT PREAMBLE: every datatype sort identifier the query mentions,
/// declared before anything that uses it.
///
/// Lever A: datatype sorts must be DECLARED before any `declare-fun` that uses
/// them. Gather every datatype declaration reachable from the formula's
/// datatype-bearing sorts, de-duplicated and topologically ordered (a
/// referenced datatype before the one that uses it). A datatype that appears
/// only as a BY-NAME reference (empty constructors — a recursive back-edge
/// whose full definition is modeled by the flat-`Ty::Adt` encoding, not as a
/// real SMT datatype) has no `declare-datatype`; it is declared as an
/// uninterpreted sort (`declare-sort … 0`) so the referencing `declare-fun`
/// is well-formed. Without this, a `(declare-fun e () Expr)` over an
/// undeclared sort `Expr` makes the whole SMT query malformed.
///
/// The walk is over [`visit_datatype_bearing_sorts`], NOT over the free
/// variables: a formula whose only datatype content is a ground
/// `Ctor`/`Sel`/`IsCtor` term has no datatype-sorted free variable at all, and
/// keying off the variables would emit the query with no preamble for it.
fn sort_mentions_datatype(sort: &Sort) -> bool {
    match sort {
        Sort::Datatype { .. } => true,
        Sort::Array(idx, elem) => sort_mentions_datatype(idx) || sort_mentions_datatype(elem),
        _ => false,
    }
}

#[must_use]
pub(crate) fn emit_sort_preamble(formula: &Formula) -> Vec<String> {
    let mut saw_datatype = false;
    let mut datatype_decls: Vec<String> = Vec::new();
    visit_datatype_bearing_sorts(formula, &mut |sort| {
        if !sort_mentions_datatype(sort) {
            return;
        }
        saw_datatype = true;
        for d in sort.datatype_declarations() {
            if !datatype_decls.contains(&d) {
                datatype_decls.push(d);
            }
        }
    });
    if !saw_datatype {
        return Vec::new();
    }
    let mut decls: Vec<String> = Vec::new();
    // Record full-datatype names so a name that has a real definition is NOT
    // also emitted as an uninterpreted sort (which would be a redeclaration).
    let mut defined_dt: BTreeSet<String> = BTreeSet::new();
    for d in &datatype_decls {
        if let Some(name) =
            d.strip_prefix("(declare-datatype ").and_then(|r| r.split_whitespace().next())
        {
            defined_dt.insert(name.to_string());
        }
    }
    let mut uninterpreted_names: BTreeSet<String> = BTreeSet::new();
    visit_datatype_bearing_sorts(formula, &mut |sort| {
        collect_uninterpreted_datatype_refs(sort, &defined_dt, &mut uninterpreted_names);
    });
    for name in &uninterpreted_names {
        decls.push(format!("(declare-sort {} 0)", escape_smtlib_symbol(name)));
    }
    decls.extend(datatype_decls);
    decls
}

/// The `(declare-fun name (<arg sorts>) <result sort>)` line for every
/// UNINTERPRETED SYMBOL the query applies.
///
/// safe-api: uninterpreted symbols need an ARITY `declare-fun`. That is the
/// predicate symbols (`Formula::Pred`, result `Bool`) AND the function symbols
/// (`Formula::FnApp`, result sort carried on the node) — an `FnApp` lowers to a
/// bare EUF application (`Formula::to_smtlib`), so without its declaration the
/// exported query references an undeclared function and the solver errors,
/// exactly as `(dir_open d)` would. Their argument Vars are declared
/// separately (the arguments are children, visited by `collect_free_vars`).
///
/// IN LOCKSTEP with the in-process lane: both declare from
/// [`uninterpreted_symbol_signatures`], which is also what `detect_logic`
/// classifies the UF dimension and the signature sorts from, so the canonical
/// transcript (and the Carcara cross-check and revalidation digest built from
/// it) declares the same symbols at the same signatures as the program ay
/// executes, under a logic that admits them.
#[must_use]
pub(crate) fn uninterpreted_symbol_declarations(formula: &Formula) -> Vec<String> {
    uninterpreted_symbol_signatures(formula)
        .into_iter()
        .map(|(name, (arg_sorts, result_sort))| {
            let params: Vec<String> = arg_sorts.iter().map(sort_to_smt2).collect();
            format!(
                "(declare-fun {} ({}) {})",
                escape_smtlib_symbol(&name),
                params.join(" "),
                sort_to_smt2(&result_sort)
            )
        })
        .collect()
}

/// Collect the names of BY-NAME datatype references (empty-constructor
/// `Sort::Datatype`) reachable from `sort`, EXCLUDING any name that already has
/// a full definition (in `defined`). These are the recursive back-edges that
/// need a `(declare-sort … 0)` so the referencing declaration is well-formed.
fn collect_uninterpreted_datatype_refs(
    sort: &Sort,
    defined: &BTreeSet<String>,
    out: &mut BTreeSet<String>,
) {
    match sort {
        Sort::Datatype { name, constructors } if constructors.is_empty() => {
            if !defined.contains(name) {
                out.insert(name.clone());
            }
        }
        Sort::Datatype { constructors, .. } => {
            for (_, fields) in constructors {
                for (_, fsort) in fields {
                    collect_uninterpreted_datatype_refs(fsort, defined, out);
                }
            }
        }
        Sort::Array(idx, elem) => {
            collect_uninterpreted_datatype_refs(idx, defined, out);
            collect_uninterpreted_datatype_refs(elem, defined, out);
        }
        _ => {}
    }
}

/// Detect the SMT-LIB2 logic name for a formula's canonical transcript.
///
/// A TOTAL FUNCTION OF THE FEATURE SET. [`analyze_formula`] computes the whole
/// feature record first — every sort position, every declared `declare-fun`
/// signature, every literal and operator — and
/// [`trust_types::logic_lattice::select_logic_name`] then makes ONE decision
/// over all the bits: the least name in the shared admissibility table
/// ([`trust_types::logic_lattice::LOGIC_LATTICE`]) that admits every feature
/// present, falling back to `ALL` when no listed name does.
///
/// WHY NOT THE OLD CASCADE. The previous implementation was a chain of early
/// returns, and a chain decides on a PREFIX of the features. Its
/// floating-point arm returned `QF_FP` for any FP formula that carried no
/// BV/array/quantifier/UF — without ever reading `has_integers` or
/// `has_reals`, which [`analyze_formula`] had computed correctly. Measured
/// shape: `And([Gt(Var(x, Int), Int(0)), FpIsNaN(f)])` was exported as
/// `(set-logic QF_FP)` over `(declare-fun __trust_u_x () Int)` — a transcript
/// declaring a sort its own logic line does not admit, in 8 of 2000 generated
/// transcripts.
///
/// THE INVARIANT now holds by construction and is proved by EXHAUSTIVE
/// ENUMERATION of the entire 2^11 feature powerset (2048 sets) in
/// `trust_types::logic_lattice`'s test
/// `every_feature_set_selects_an_admitting_logic`:
///
/// * ADMISSIBILITY — for every feature set `S`, the chosen name admits every
///   feature in `S`. So the `(set-logic …)` line always admits the sorts its
///   own `(declare-*)` lines write and the operators its own `(assert …)`
///   applies. `smt2_self_consistency_tests` checks the same property from the
///   other end, by PARSING the emitted text against the same table.
///
/// MONOTONICITY IS NOT CLAIMED, and the table does not have it. THIS function
/// is a SINGLE-FORMULA caller and does not need it: it selects once, from the
/// complete record of the one formula it is about to emit. The MULTI-formula
/// callers — the function-group and session logic in `incremental_ay` — do not
/// call this function per member and combine the NAMES; they fold
/// [`formula_features`] over their members with `Theories::union_all` and
/// select ONCE from the union, which admissibility alone covers. See
/// `trust_types::logic_lattice::select_logic_name` for the audit of every call
/// site, and that module's header for the exact characterization of where
/// monotonicity fails (751 of 177_147 subset pairs, all with a source set no
/// row names exactly).
///
/// THE LEVERS the old cascade spelled out by hand are now table rows, and the
/// soundness argument for each is unchanged — a WIDER logic only enlarges the
/// admissible theory set, never a formula's models, so it cannot turn a SAT
/// violation into UNSAT (no false prove):
///
/// * datatypes (LEVER A, RE-POINTED 2026-09-18): twelve `*DT*` rows now name
///   the datatype fragments, so a datatype-bearing sort — a variable's, a
///   `Ctor` result sort, a `Sel` field sort, a tester's datatype name, a
///   binder's, or one written into a `declare-fun` SIGNATURE — selects an
///   SMT-LIB `DT` name where one is attested, and `ALL` where none is (the
///   `A`-leading `DT` names are deliberately absent). MEASURED SAFE: ay's
///   in-process gate maps EVERY name containing `DT` to `Logic::All` before it
///   routes, so the re-point cannot change which pipeline a query takes, and
///   8 queries × 19 candidate names came back byte-identical to `ALL`;
/// * bitvectors mixed with integers and reals (LEVER C, CLOSED 2026-09-18): all
///   EIGHT names are rows — `QF_UFBVLIA` and `QF_AUFBVLIA`, which came in when
///   the lever was split, plus `UFBVLIA`, `QF_AUFBVNIA` and the four
///   `*BVFPLRA` names, which had been held out ONLY because ay's IN-PROCESS
///   parser refuses them. That was never a property of the name: it is a
///   property of one consumer, and it is now handled at that consumer by
///   `in_process_ay_backend::native_lane_logic`, which re-selects the NATIVE
///   lane's header from the sublattice that parser accepts. `{BitVectors,
///   Reals}` therefore gets its first name, `QF_BVFPLRA`, in THIS lane. WHEN
///   THAT WAS WRITTEN the native lane's header was unchanged for all 1024
///   feature sets, because that parser refused all six; re-measured 2026-09-19
///   against ay `9d2cda9c8727` it accepts all six, so the SAME 53 feature sets
///   move on the native lane too and the two lanes now write the same header
///   everywhere.
///   THE OLD JUSTIFICATION HERE WAS RE-MEASURED AND REFUTED: this note used to cite a
///   five-line query (`_45: Int`, `heap: Array Int Int`, `(= _45 7)`) as
///   `unknown` + MODEL-UNCONFIRMED under `QF_AUFBV` and `sat` under `ALL`. At
///   today's ay pin four of five re-measured shapes come back DECIDED under
///   `QF_AUFBV`, three with a strict-verified UNSAT artifact, and the one
///   `unknown` reproduces IDENTICALLY under `ALL` — it is a property of ay's
///   combined BV+LIA SAT lane, not of the header;
/// * floating point: `QF_FP` is admissible only for the PURE fragment; mixed
///   with any other theory — including the `Int`/`Real` arithmetic the old
///   cascade skipped past — the answer is `ALL`;
/// * DIFFERENCE LOGIC (the tenth dimension, added 2026-09-18): `QF_IDL` and
///   `QF_RDL` are rows, reachable only from a formula whose every arithmetic
///   atom is provably in SMT-LIB's difference grammar. [`analyze_formula`]
///   charges `Theories::WIDE_ARITH` for anything else, so an ordinary integer
///   transcript still heads `QF_LIA`.
///
/// `smtlib_backend::generate_smtlib_script` and `in_process_ay_backend`'s
/// `problem_smt2` call THIS function, and `trust_types::smt_logic::select_logic`
/// calls the same selector with its own (UF-less) feature walk, so every lane in
/// the workspace maps a feature set to a name through one table.
///
/// ONE LANE DOES NOT CALL THIS FUNCTION, DELIBERATELY. `in_process_ay_backend`'s
/// NATIVE `set_logic` calls `native_lane_logic` on the SAME record
/// ([`formula_features`]) instead, because the linked
/// `ay_bindings::execute_direct` path carries its own logic-name parser and
/// aborts the whole solve on a name it does not know. That is a narrowing at
/// the consumer, not a second table: the rows, the order and the first-minimum
/// rule are this one's, and the restriction is provably a NO-OP wherever this
/// function's answer is a name that parser already accepts. MEASURED 2026-09-19
/// at ay `9d2cda9c8727`, that parser accepts EVERY row, so the narrowing is a
/// no-op for all 2048 feature sets and the two lanes agree on every header. It
/// stays where it is: `HORN` is still refused there, and a narrowing in ay must
/// fail a test rather than silently cost a verdict.
#[must_use]
pub(crate) fn detect_logic(formula: &Formula) -> &'static str {
    trust_types::logic_lattice::select_logic_name(formula_features(formula))
}

/// The THEORY FEATURE RECORD of `formula`, as the transcript lane sees it —
/// [`detect_logic`] without the final selection.
///
/// This is what a MULTI-FORMULA caller needs. One `(set-logic L)` covering
/// several queries must satisfy `admits(L) ⊇ features(f1) ∪ … ∪ features(fn)`,
/// and the only way to get that from a selector that is not monotone is to take
/// the union FIRST and select ONCE:
///
/// ```ignore (illustrative)
/// let joint = Theories::union_all(vcs.iter().map(|vc| formula_features(&vc.formula)));
/// let logic = trust_types::logic_lattice::select_logic_name(joint);
/// ```
///
/// `incremental_ay::detect_group_logic` and the session-wide base logic both do
/// exactly this. Selecting per member and picking the "widest" NAME would be
/// wrong: the names are not totally ordered by admission, which is what
/// `logic_lattice`'s `monotonicity_fails_only_from_sets_no_row_names_exactly`
/// records.
#[must_use]
pub(crate) fn formula_features(formula: &Formula) -> Theories {
    analyze_formula(formula)
}

// --- Internal helpers ---

/// The canonical BY-NAME datatype reference for `name`: a `Sort::Datatype` with
/// EMPTY constructors, the same shape a recursive back-edge already uses. It
/// contributes no `declare-datatype` and, unless a full definition of the same
/// name is also in scope, becomes a `(declare-sort <name> 0)`.
fn by_name_datatype(name: &str) -> Sort {
    Sort::Datatype { name: name.to_string(), constructors: Vec::new() }
}

/// Hand every sort carried anywhere in `formula` that could be datatype-bearing
/// to `f`, in a deterministic pre-order walk of the whole tree.
///
/// `Var`/`SymVar` sorts are the classic source, but they are NOT the whole
/// datatype surface of `Formula`: `Ctor` carries its result (datatype) sort,
/// `Sel` carries the selected field's sort, `FnApp` carries its application
/// result sort, quantifier bindings carry their bound sorts, and both `Sel` and
/// `IsCtor` name the datatype they range over. A formula whose only datatype
/// content is a GROUND constructor term reaches none of that through a `Var`,
/// so a `Var`/`SymVar`-only rule would pick a non-`ALL` logic AND emit no
/// datatype preamble — a malformed query on the text lane and an undeclared
/// datatype on the in-process lane.
///
/// `Sel`/`IsCtor` know their datatype only BY NAME, so a by-name reference is
/// synthesized for it (see [`by_name_datatype`]); a full definition of the same
/// name found elsewhere in the formula still wins, because the caller records
/// defined names before it collects the uninterpreted ones.
///
/// Both SMT lanes walk through this one function so the canonical text
/// transcript and the native AY program cannot disagree about which datatype
/// sorts the query mentions.
///
/// THE ONE INVENTORY. The sort positions themselves are not re-spelled here:
/// they come from `trust_types::smt_logic::visit_node_sort_positions`, the
/// single list `DatatypeDefs::extend_from_formula`, `unlowerable_sort_position`
/// and `select_logic` also read. This function adds exactly one thing on top —
/// the BY-NAME datatype reference a `Sel`/`IsCtor` carries as a bare `&str`
/// rather than a `Sort` — and `detect_logic`, `emit_declarations` and
/// `disjoint_components` all consume THIS function, so the logic line, the
/// declarations and the component split see the same sorts by construction.
pub(crate) fn visit_datatype_bearing_sorts(formula: &Formula, f: &mut impl FnMut(&Sort)) {
    trust_types::visit_formula_nodes(formula, &mut |node| {
        trust_types::smt_logic::visit_node_sort_positions(node, f);
        // `Sel`/`IsCtor` know their datatype only BY NAME, so it has no `Sort`
        // field for the inventory to hand over; synthesize the canonical
        // by-name reference for it. Emitted AFTER the node's own sort
        // positions, which for `Sel` means `field_sort` first — the order
        // `emit_declarations` dedups its preamble in.
        if let Some(name) = trust_types::smt_logic::node_named_datatype_reference(node) {
            f(&by_name_datatype(name));
        }
    });
}

/// Analyze a formula for the theory features its transcript requires.
///
/// Returns the SHARED feature record
/// ([`trust_types::logic_lattice::Theories`]) that [`detect_logic`] hands to
/// the shared selector. No name is chosen here: this function only SEES, and
/// the whole record is complete before anything decides.
///
/// ONE SHARED TRAVERSAL, not a fourth parallel walker. The bits come from
/// exactly three sources, and each is a source the TRANSCRIPT ITSELF is written
/// from, so the `(set-logic …)` line cannot admit less than the declarations
/// and the assertion beside it use:
///
/// 1. **Sort positions** — [`visit_datatype_bearing_sorts`], the same walk
///    `emit_declarations` uses to write the `(declare-sort …)`,
///    `(declare-datatype …)` and `(declare-fun x () S)` lines, and (through
///    `trust_types::smt_logic::visit_node_sort_positions`) the same list
///    `DatatypeDefs::extend_from_formula` and the router's
///    `unlowerable_sort_position` gate read. Previously this function
///    classified only TWO of the six positions (`Var`/`SymVar`) plus the
///    binders, so a `Ctor`/`FnApp` result sort and a `Sel` field sort were
///    declared but never classified.
///
/// 2. **Literals and operators** —
///    [`trust_types::logic_lattice::node_theories`], the same per-node
///    classifier `trust_types::smt_logic::select_logic` reads, so the library
///    selector and the transcript selector cannot disagree about what an
///    `fp.*` or `bv*` node needs. That classification is complete, and provably
///    so, by induction over the sorts a term can have. Every term of sort
///
///    * `BitVec` is a `BitVec` literal, a `Bv*` operator, `IntToBv`,
///      `FpToIeeeBv`, `FpToSbv`/`FpToUbv`, a `Select` from a BV-element array,
///      or a sort position (`Var`/`SymVar`/`Ctor`/`Sel`/`FnApp`/binder);
///    * `Float`/`RoundingMode` is an `Fp*` literal or operator,
///      `FpFromBits`/`FpFromSbv`/`FpFromUbv`/`FpConvert`, a `Select`, or a sort
///      position;
///    * `Int` is an `Int`/`UInt` literal, `BvToInt`, a `Select`, or a sort
///      position — the arithmetic nodes (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Neg`)
///      and `Ite` are sort-GENERIC and carry the SORT theory of their operands,
///      which are themselves covered by this same induction. `Mul`, `Div` and
///      `Rem` additionally carry `Theories::NONLINEAR` when their operands make
///      them nonlinear (a product of two non-literals, a division or remainder
///      by a non-literal), which is a LINEARITY qualifier rather than a sort
///      and comes from the same shared `node_theories` — so a `(* x y)` in a
///      transcript is headed `QF_NIA`, not `QF_LIA`, on THIS lane too, with no
///      edit here;
///    * `Real` is a `Rat` literal, a `Select`, or a sort position;
///    * `Array` is a `Store`, an `Ite`, or a sort position;
///    * a datatype is a `Ctor`, `Sel`, `IsCtor` or a sort position — all of
///      which reach `Theories::DATATYPES` through (1);
///    * `Bool` needs no theory.
///
///    So a node with no arm can only be one whose theory content is already
///    carried by a child or by a sort position — or a FUTURE
///    `#[non_exhaustive]` variant, which the router declines outright
///    (`is_lowerable_formula`) before this function is consulted.
///
/// 3. **Declared signatures** — [`uninterpreted_symbol_signatures`], the same
///    map `emit_declarations` writes the `(declare-fun f (A B) R)` lines from
///    and `build_program` declares natively from. Every sort in a signature is
///    a sort the transcript writes, so each is classified here. The UF bit is
///    set for a signature of arity >= 1 only: a 0-ary `declare-fun` is an
///    ordinary free constant, which every SMT-LIB logic admits — exactly the
///    rule `smt2_self_consistency_tests` charges `Req::Uf` by, so the selector
///    and the checker agree on what "needs UF" means. Previously only
///    `Formula::Pred` set that bit, so an `FnApp` — which lowers to a bare EUF
///    application and IS declared — headed a `QF_*` logic with no UF at all.
fn array_sort_theories_ref(index: &Sort, element: &Sort) -> Theories {
    let theories = Theories::ARRAYS
        .union(trust_types::logic_lattice::sort_theories(index))
        .union(trust_types::logic_lattice::sort_theories(element));
    match (index, element) {
        (Sort::Int, Sort::Int) => theories,
        (Sort::BitVec(i), Sort::BitVec(j)) if *i > 0 && *j > 0 => theories,
        _ => theories.union(Theories::WIDE_ARRAY),
    }
}

fn analyze_formula(formula: &Formula) -> Theories {
    let mut features = Theories::NONE;
    let mut has_uninterpreted_app = false;

    // (1) + (2) FUSED SINGLE WALK: sort positions, by-name `Sel`/`IsCtor`
    // datatype references, literals and operators (`node_theories`), and an
    // uninterpreted-application presence flag (`Pred`/`FnApp`) so pure-theory
    // formulas pay only ONE AST pass with zero `ConstArray`/`by_name_datatype`
    // heap allocations.
    trust_types::visit_formula_nodes(formula, &mut |node| {
        match node {
            Formula::ConstArray { index_sort, elem_sort, .. } => {
                features.insert(array_sort_theories_ref(index_sort, elem_sort));
            }
            _ => {
                trust_types::smt_logic::visit_node_sort_positions(node, &mut |sort| {
                    features.insert(trust_types::logic_lattice::sort_theories(sort));
                });
            }
        }
        if trust_types::smt_logic::node_named_datatype_reference(node).is_some() {
            features.insert(Theories::DATATYPES);
        }
        features.insert(trust_types::logic_lattice::node_theories(node));
        if matches!(node, Formula::Pred(..) | Formula::FnApp { .. }) {
            has_uninterpreted_app = true;
        }
    });

    // (3) DECLARED SIGNATURES — the declarations' own signature map. A symbol
    // in it is a `(declare-fun …)` line in the transcript and an application in
    // the assertion, so the logic must admit every sort the line names, and —
    // at arity >= 1 — uninterpreted functions. Only populated when at least one
    // `Pred` or `FnApp` node exists in `formula`.
    if has_uninterpreted_app {
        for (_, (arg_sorts, result_sort)) in uninterpreted_symbol_signatures(formula) {
            if !arg_sorts.is_empty() {
                features.insert(Theories::UF);
            }
            for arg_sort in &arg_sorts {
                features.insert(trust_types::logic_lattice::sort_theories(arg_sort));
            }
            features.insert(trust_types::logic_lattice::sort_theories(&result_sort));
        }
    }

    // (4) LINEAR FORM — the DIFFERENCE-fragment qualifier, which is the one
    // dimension no per-node classifier can decide: `Theories::WIDE_ARITH` is a
    // property of a whole ATOM (`(- x y) < 3` is in SMT-LIB's `QF_IDL` grammar,
    // `x + y < 3` is not), so `node_theories` cannot charge it and steps (1)
    // and (2) above cannot see it.
    //
    // THIS LINE IS LOAD-BEARING. Without it this lane would hand
    // `select_logic_name` a record carrying `INTS` and no `WIDE_ARITH` for
    // EVERY integer query, and the selector would answer `QF_IDL` — a header
    // NARROWER than the transcript under it, and a silent one: ay maps
    // `QF_IDL` onto its full `QfLia` solver and enforces no restriction, so
    // every in-house verdict would stay correct and only an external replayer
    // would reject the evidence. `features_carry_the_linear_form_bit` pins it.
    // Gated on `INTS | REALS` exactly as `trust_types::logic_lattice::formula_theories`:
    // `wide_arithmetic_theories` only ever charges `WIDE_ARITH` on atoms whose
    // subtrees already contribute `INTS` or `REALS` under steps (1) and (2).
    if features.contains(Theories::INTS) || features.contains(Theories::REALS) {
        features.insert(trust_types::logic_lattice::wide_arithmetic_theories(formula));
    }

    features
}

/// Collect all free variables (name, sort) from a formula, excluding
/// quantifier-bound names.
///
/// DELEGATES to [`trust_types::collect_free_var_decls`], which is now the ONE
/// free-variable collector in the workspace. It used to be a second,
/// independent scope-tracking walk that happened to agree with the trust-types
/// one on every shape anyone had tried; the traversal audit that called this
/// function "the single free-variable collector" had simply not listed the
/// other one. They did NOT agree everywhere: the trust-types collector asked
/// `Formula::free_variables()` for the free NAMES and then took every
/// `Var`/`SymVar` node with such a name, so a name bound in one subterm and
/// free in another produced two `(declare-fun …)` lines at two different sorts.
/// That collector now tracks binder scope structurally — this body — and both
/// callers share it, so the divergence cannot come back by editing one copy.
pub(crate) fn collect_free_vars(formula: &Formula) -> BTreeSet<(String, Sort)> {
    trust_types::collect_free_var_decls(formula)
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    // --- Helpers ---

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    fn bv_var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }

    // -- Lever A: datatype preamble emission --------------------------------

    /// A by-name recursive-datatype reference (the shape the minimal Lever A
    /// lowering produces for a recursive ADT value) must (1) select a
    /// datatype-capable logic and (2) be DECLARED — as an uninterpreted sort —
    /// BEFORE the `declare-fun` that uses it, so the SMT query is well-formed.
    #[test]
    fn by_name_datatype_var_emits_declare_sort_before_declare_fun() {
        let dt = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), dt.clone())),
            Box::new(Formula::Var("e".into(), dt)),
        );
        // Lever A, re-pointed 2026-09-18: the narrowest attested SMT-LIB name
        // for "datatypes and nothing else". Still datatype-capable, and still
        // `Logic::All` at ay's `parse_logic` (`contains("DT")`).
        assert_eq!(
            detect_logic(&f),
            "QF_DT",
            "a datatype var must select a datatype-capable logic"
        );

        let decls = emit_declarations(&f);
        let sort_pos = decls.iter().position(|d| d.contains("(declare-sort Expr 0)"));
        let fun_pos = decls.iter().position(|d| d.contains("(declare-fun e () Expr)"));
        assert!(sort_pos.is_some(), "Expr must be declared as a sort: {decls:?}");
        assert!(fun_pos.is_some(), "e must be declared with sort Expr: {decls:?}");
        assert!(
            sort_pos < fun_pos,
            "the sort declaration must precede the const that uses it: {decls:?}"
        );
    }

    /// A FULL datatype sort emits a `declare-datatype` (not a bare sort), and the
    /// recursive self-reference inside it stays a by-name `Expr` (finite output).
    #[test]
    fn full_datatype_var_emits_declare_datatype() {
        let expr_ref = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let full = Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), expr_ref.clone()), ("x".into(), expr_ref)]),
            ],
        };
        let f = Formula::Eq(
            Box::new(Formula::Var("e".into(), full.clone())),
            Box::new(Formula::Var("e".into(), full)),
        );
        let decls = emit_declarations(&f);
        let dt_pos = decls.iter().position(|d| d.contains("(declare-datatype Expr"));
        assert!(dt_pos.is_some(), "a full datatype var must emit a declare-datatype: {decls:?}");
        // Exactly one datatype declaration (self-recursion is by-name, not expanded).
        assert_eq!(
            decls.iter().filter(|d| d.contains("declare-datatype")).count(),
            1,
            "self-recursion must not duplicate the datatype declaration: {decls:?}"
        );
        // And NOT also a redundant (declare-sort Expr 0).
        assert!(
            !decls.iter().any(|d| d.contains("(declare-sort Expr 0)")),
            "a fully-defined datatype must not also be declared as an uninterpreted sort: {decls:?}"
        );
        // The definition still precedes the const that uses it.
        let fun_pos = decls.iter().position(|d| d.contains("(declare-fun e () Expr)"));
        assert!(fun_pos.is_some(), "e must be declared with sort Expr: {decls:?}");
        assert!(dt_pos < fun_pos, "declare-datatype must precede its uses: {decls:?}");
    }

    /// The recursive `Expr` shape used by the `Ctor`/`Sel`/`IsCtor` tests: a
    /// `Const(c: bv32)` leaf and a binary `App(f: Expr, x: Expr)` node whose
    /// children are by-name back-edges.
    fn expr_dt_sort() -> Sort {
        let r = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), r.clone()), ("x".into(), r)]),
            ],
        }
    }

    /// A GROUND constructor term — the datatype sort is carried by
    /// `Formula::Ctor`, and NO free variable has a datatype sort anywhere in the
    /// formula. It must still (i) select the datatype-capable `ALL` logic and
    /// (ii) emit its `declare-datatype` BEFORE the `declare-fun`s. Keying
    /// detection off `Var`/`SymVar` alone silently produced a non-`ALL` logic
    /// and no preamble at all, i.e. a malformed SMT2 script.
    #[test]
    fn ground_ctor_only_datatype_declares_before_declare_funs() {
        let ground = Formula::Ctor {
            ctor: "Const".into(),
            args: vec![Formula::BitVec { value: 1, width: 32 }],
            sort: expr_dt_sort(),
        };
        // `n == 0 AND (Const 1) == (Const 1)`: the Int var forces a declare-fun
        // to order the datatype declaration against, and is not datatype-sorted.
        let f = Formula::And(vec![
            Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(ground.clone()), Box::new(ground)),
        ]);

        // Precondition of the regression: nothing datatype-sorted is reachable
        // through a free variable, so the old Var-only rule saw no datatype.
        assert!(
            collect_free_vars(&f).iter().all(|(_, s)| !s.contains_datatype()),
            "this test is only meaningful when no FREE VAR carries a datatype sort"
        );

        assert_eq!(detect_logic(&f), "ALL", "a ground Ctor term still needs the datatype theory");

        let decls = emit_declarations(&f);
        let dt_pos = decls.iter().position(|d| d.contains("(declare-datatype Expr"));
        let fun_pos = decls.iter().position(|d| d.starts_with("(declare-fun "));
        assert!(dt_pos.is_some(), "the Ctor's datatype must be declared: {decls:?}");
        assert!(fun_pos.is_some(), "n must still be declared: {decls:?}");
        assert!(dt_pos < fun_pos, "declare-datatype must precede every declare-fun: {decls:?}");
        assert!(
            !decls.iter().any(|d| d.contains("(declare-sort Expr 0)")),
            "a fully-defined datatype must not also be an uninterpreted sort: {decls:?}"
        );
    }

    /// A selector application and a constructor tester name their datatype only
    /// BY NAME. With no full definition in scope they must still select `ALL`
    /// and emit `(declare-sort Expr 0)` ahead of the `declare-fun`s, so the
    /// sort identifier the query mentions is in scope.
    #[test]
    fn sel_and_is_ctor_only_datatype_emits_declare_sort_before_declare_funs() {
        let e = Formula::Var("e".into(), Sort::Int); // deliberately NOT datatype-sorted
        for f in [
            Formula::Eq(
                Box::new(Formula::Sel {
                    datatype: "Expr".into(),
                    field: "c".into(),
                    field_sort: Sort::BitVec(32),
                    arg: Box::new(e.clone()),
                }),
                Box::new(Formula::BitVec { value: 0, width: 32 }),
            ),
            Formula::IsCtor { datatype: "Expr".into(), ctor: "Const".into(), arg: Box::new(e) },
        ] {
            assert!(
                collect_free_vars(&f).iter().all(|(_, s)| !s.contains_datatype()),
                "this test is only meaningful when no FREE VAR carries a datatype sort"
            );
            // `{Datatypes, Ints, …}`: `Sel`'s bitvector field sort takes the
            // first shape to `ALL` (no attested `A`-free `BVDT`+`Int` name),
            // while `IsCtor` over an `Int` argument heads `QF_UFDTLIA`. Both
            // are datatype-capable, which is what this test is about.
            let logic = detect_logic(&f);
            assert!(
                logic == "ALL" || logic.contains("DT"),
                "Sel/IsCtor range over a datatype: {f:?} headed `{logic}`"
            );

            let decls = emit_declarations(&f);
            let sort_pos = decls.iter().position(|d| d.contains("(declare-sort Expr 0)"));
            let fun_pos = decls.iter().position(|d| d.starts_with("(declare-fun "));
            assert!(sort_pos.is_some(), "Expr must be declared as a sort: {decls:?}");
            assert!(fun_pos.is_some(), "e must still be declared: {decls:?}");
            assert!(sort_pos < fun_pos, "declare-sort must precede every declare-fun: {decls:?}");
        }
    }

    /// A datatype reached ONLY through a quantifier binder — the sort lives in
    /// the `(forall ((e Expr)) …)` binding list, which is not a `children()`
    /// edge — must still be declared before it is used.
    #[test]
    fn quantifier_bound_datatype_sort_is_declared() {
        let f = Formula::Forall(
            vec![("e".into(), expr_dt_sort())],
            Box::new(Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(0)))),
        );
        // `{Quantifiers, Datatypes, BitVectors, Ints, WideArith}` — the bound
        // sort's `Const` field is a bitvector and the body compares an `Int`.
        // SMT-LIB's only names for that mix are the `A`-leading `AUFBVDT*`
        // ones, which the table declines for want of an [S1] declaration of
        // their array fragment, so the honest answer is the top. What this test
        // is about is that the BINDER SORT REACHED the logic line at all.
        assert_eq!(detect_logic(&f), "ALL", "a datatype binder needs the datatype theory");
        let decls = emit_declarations(&f);
        let dt_pos = decls.iter().position(|d| d.contains("(declare-datatype Expr"));
        let fun_pos = decls.iter().position(|d| d.starts_with("(declare-fun "));
        assert!(dt_pos.is_some(), "the bound sort's datatype must be declared: {decls:?}");
        assert!(dt_pos < fun_pos, "declare-datatype must precede every declare-fun: {decls:?}");
    }

    /// A formula with NO datatype content keeps its precise (non-`ALL`) logic and
    /// emits no sort-declaration preamble — Lever A must not perturb the
    /// existing scalar path.
    #[test]
    fn non_datatype_formula_keeps_precise_logic_and_empty_preamble() {
        let f = Formula::BvAdd(Box::new(bv_var("x", 32)), Box::new(bv_var("y", 32)), 32);
        assert_eq!(detect_logic(&f), "QF_BV");
        let decls = emit_declarations(&f);
        assert!(
            !decls.iter().any(|d| d.contains("declare-sort") || d.contains("declare-datatype")),
            "no datatype content must emit no datatype preamble: {decls:?}"
        );
    }

    // --- formula_to_smt2 tests ---

    #[test]
    fn test_formula_to_smt2_bool_literals() {
        assert_eq!(formula_to_smt2(&Formula::Bool(true)), "true");
        assert_eq!(formula_to_smt2(&Formula::Bool(false)), "false");
    }

    #[test]
    fn test_formula_to_smt2_int_literals() {
        assert_eq!(formula_to_smt2(&Formula::Int(0)), "0");
        assert_eq!(formula_to_smt2(&Formula::Int(42)), "42");
        assert_eq!(formula_to_smt2(&Formula::Int(-7)), "(- 7)");
    }

    #[test]
    fn test_formula_to_smt2_uint_literal() {
        assert_eq!(formula_to_smt2(&Formula::UInt(u128::MAX)), u128::MAX.to_string());
    }

    #[test]
    fn test_formula_to_smt2_bitvec_literal() {
        assert_eq!(formula_to_smt2(&Formula::BitVec { value: 10, width: 32 }), "(_ bv10 32)");
    }

    #[test]
    fn test_formula_to_smt2_variables() {
        assert_eq!(formula_to_smt2(&int_var("x")), "x");
        assert_eq!(formula_to_smt2(&bv_var("y", 64)), "y");
    }

    #[test]
    fn test_formula_to_smt2_boolean_connectives() {
        let p = Formula::Var("p".into(), Sort::Bool);
        let q = Formula::Var("q".into(), Sort::Bool);

        assert_eq!(formula_to_smt2(&Formula::Not(Box::new(p.clone()))), "(not p)");
        assert_eq!(formula_to_smt2(&Formula::And(vec![p.clone(), q.clone()])), "(and p q)");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![p.clone(), q.clone()])), "(or p q)");
        assert_eq!(formula_to_smt2(&Formula::Implies(Box::new(p), Box::new(q))), "(=> p q)");
    }

    #[test]
    fn test_formula_to_smt2_arithmetic() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Add(Box::new(a.clone()), Box::new(b.clone()))),
            "(+ a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Sub(Box::new(a.clone()), Box::new(b.clone()))),
            "(- a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Mul(Box::new(a.clone()), Box::new(b.clone()))),
            "(* a b)"
        );
        // soundness (round-7): Rust `/` and `%` are TRUNCATED, so they lower
        // to the sign-corrected encoding (not bare Euclidean div/mod). See
        // trust-types/src/formula/smtlib.rs.
        assert_eq!(
            formula_to_smt2(&Formula::Div(Box::new(a.clone()), Box::new(b.clone()))),
            "(div (- a (ite (>= a 0) (mod a b) (- (mod (- a) b)))) b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Rem(Box::new(a.clone()), Box::new(b.clone()))),
            "(ite (>= a 0) (mod a b) (- (mod (- a) b)))"
        );
        assert_eq!(formula_to_smt2(&Formula::Neg(Box::new(a))), "(- a)");
    }

    #[test]
    fn test_formula_to_smt2_comparisons() {
        let a = int_var("a");
        let b = int_var("b");

        assert_eq!(
            formula_to_smt2(&Formula::Eq(Box::new(a.clone()), Box::new(b.clone()))),
            "(= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
            "(< a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Le(Box::new(a.clone()), Box::new(b.clone()))),
            "(<= a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
            "(> a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Ge(Box::new(a.clone()), Box::new(b.clone()))),
            "(>= a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bitvector_ops() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvAdd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvadd a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSub(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsub a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvAnd(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvand a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvNot(Box::new(a.clone()), 32)), "(bvnot a)");
        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLe(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsle a b)"
        );
    }

    #[test]
    fn test_formula_to_smt2_bv_conversions() {
        let x = bv_var("x", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvToInt(Box::new(x.clone()), 32, false)),
            "(bv2nat x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::IntToBv(Box::new(int_var("n")), 32)),
            "((_ int2bv 32) n)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvExtract { inner: Box::new(x.clone()), high: 15, low: 0 }),
            "((_ extract 15 0) x)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvConcat(Box::new(x.clone()), Box::new(bv_var("y", 32)))),
            "(concat x y)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvZeroExt(Box::new(x.clone()), 32)),
            "((_ zero_extend 32) x)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSignExt(Box::new(x), 16)), "((_ sign_extend 16) x)");
    }

    #[test]
    fn test_formula_to_smt2_quantifiers() {
        let body = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let forall = Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(body.clone()));
        assert_eq!(formula_to_smt2(&forall), "(forall ((x Int)) (> x 0))");

        let exists = Formula::Exists(vec![("x".into(), Sort::Int)], Box::new(body));
        assert_eq!(formula_to_smt2(&exists), "(exists ((x Int)) (> x 0))");
    }

    /// The BINDER-SORT hole in logic detection. A quantifier's binding sorts
    /// are not `Formula::children()`, so `detect_logic`'s walk never saw them:
    /// a binder whose bound variable is not USED in the body contributed no
    /// theory at all, and the emitted `(set-logic …)` disagreed with the
    /// declarations `emit_declarations` produced from the same binder list.
    #[test]
    fn a_quantifier_binder_sort_reaches_logic_detection() {
        // The bound variable is deliberately UNUSED, so only the binder sort
        // itself can carry the theory.
        let trivial = || Box::new(Formula::Bool(true));
        for (sort, expected) in [
            (Sort::BitVec(8), "BV"),
            (Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)), "A"),
            (Sort::Real, "R"),
            (Sort::Float { eb: 8, sb: 24 }, "FP"),
        ] {
            let quantified = Formula::Forall(vec![("q".into(), sort.clone())], trivial());
            let logic = detect_logic(&quantified);
            assert!(
                logic.contains(expected) || logic == "ALL",
                "a {sort:?} binder must reach logic detection, got {logic}"
            );
            assert_ne!(logic, "QF_LIA", "{sort:?} binder mis-detected as {logic}");
        }
    }

    #[test]
    fn test_formula_to_smt2_arrays() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let idx = Formula::Int(0);
        let val = Formula::Int(42);

        assert_eq!(
            formula_to_smt2(&Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()))),
            "(select arr 0)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::Store(Box::new(arr), Box::new(idx), Box::new(val))),
            "(store arr 0 42)"
        );
    }

    #[test]
    fn test_formula_to_smt2_ite() {
        let f = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Int(1)),
            Box::new(Formula::Int(0)),
        );
        assert_eq!(formula_to_smt2(&f), "(ite true 1 0)");
    }

    // --- sort_to_smt2 tests ---

    #[test]
    fn test_sort_to_smt2_basic() {
        assert_eq!(sort_to_smt2(&Sort::Bool), "Bool");
        assert_eq!(sort_to_smt2(&Sort::Int), "Int");
        assert_eq!(sort_to_smt2(&Sort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(
            sort_to_smt2(&Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))),
            "(Array Int Int)"
        );
    }

    #[test]
    fn test_sort_to_smt2_nested_array() {
        let nested = Sort::Array(
            Box::new(Sort::BitVec(64)),
            Box::new(Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool))),
        );
        assert_eq!(sort_to_smt2(&nested), "(Array (_ BitVec 64) (Array Int Bool))");
    }

    // --- emit_declarations tests ---

    #[test]
    fn test_emit_declarations_simple() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0], "(declare-fun x () Int)");
        assert_eq!(decls[1], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_includes_symbol_variables() {
        let f = Formula::SymVar(Symbol::intern("interned_bits"), Sort::BitVec(32));
        assert_eq!(emit_declarations(&f), vec!["(declare-fun interned_bits () (_ BitVec 32))"]);
        assert_eq!(detect_logic(&f), "QF_BV");
    }

    #[test]
    fn test_emit_declarations_excludes_bound_symbol_variables() {
        let f = Formula::Forall(
            vec![(Symbol::intern("q"), Sort::Int)],
            Box::new(Formula::Eq(
                Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Int)),
                Box::new(Formula::SymVar(Symbol::intern("free"), Sort::Int)),
            )),
        );
        assert_eq!(emit_declarations(&f), vec!["(declare-fun free () Int)"]);
    }

    #[test]
    fn test_emit_declarations_respects_lexical_quantifier_shadowing() {
        let f = Formula::And(vec![
            Formula::Eq(
                Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Int)),
                Box::new(Formula::Int(7)),
            ),
            Formula::Forall(
                vec![(Symbol::intern("q"), Sort::Bool)],
                Box::new(Formula::Eq(
                    Box::new(Formula::SymVar(Symbol::intern("q"), Sort::Bool)),
                    Box::new(Formula::Bool(true)),
                )),
            ),
        ]);
        assert_eq!(emit_declarations(&f), vec!["(declare-fun q () Int)"]);
    }

    /// The PURE float fragment heads `QF_FP`; the moment a BITVECTOR joins it,
    /// the transcript is in the COMBINED BV+FP fragment and heads `QF_BVFP`.
    ///
    /// Both names are SMT-LIB's. The mixed case answered `ALL` until the
    /// SMT-LIB name audit added the floating-point family to the shared table —
    /// sound, since `ALL` admits strictly more, but it sent every `fp.to_ieee_bv`
    /// / `FpConst` transcript to the top of the lattice for want of a row, and
    /// `QF_BVFP` is precisely the fragment SMT-LIB puts that form in.
    #[test]
    fn test_detect_logic_for_floating_point_and_fp_bv_mix() {
        let fp_sort = Sort::Float { eb: 8, sb: 24 };
        let fp = Formula::FpEq(
            Box::new(Formula::SymVar(Symbol::intern("f"), fp_sort.clone())),
            Box::new(Formula::FpZero { neg: false, eb: 8, sb: 24 }),
        );
        assert_eq!(detect_logic(&fp), "QF_FP");
        assert_eq!(emit_declarations(&fp), vec!["(declare-fun f () (_ FloatingPoint 8 24))"]);

        let fp_bits = Formula::Eq(
            Box::new(Formula::FpToIeeeBv(Box::new(Formula::SymVar(
                Symbol::intern("f"),
                fp_sort.clone(),
            )))),
            Box::new(Formula::BitVec { value: 0, width: 32 }),
        );
        assert_eq!(detect_logic(&fp_bits), "QF_BVFP");

        // An INTEGER beside the float is still the top: SMT-LIB's only names
        // for floats-with-integers are the four `*FPDT*` ones, which drag
        // DATATYPES and NONLINEARITY in with them — a separate rejection with
        // its own reason, untouched when Lever A was re-pointed. This is the M1
        // shape and it has not moved.
        let fp_and_int = Formula::And(vec![
            fp,
            Formula::Gt(
                Box::new(Formula::SymVar(Symbol::intern("n"), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        assert_eq!(detect_logic(&fp_and_int), "ALL");
    }

    #[test]
    fn test_emit_declarations_deduplicates() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(int_var("x")));
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
    }

    #[test]
    fn test_emit_declarations_excludes_quantifier_bound() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Add(Box::new(int_var("x")), Box::new(int_var("y")))),
        );
        let decls = emit_declarations(&f);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0], "(declare-fun y () Int)");
    }

    #[test]
    fn test_emit_declarations_no_vars() {
        let f = Formula::Bool(true);
        let decls = emit_declarations(&f);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_emit_declarations_bitvec_sort() {
        let f = bv_var("bits", 64);
        let decls = emit_declarations(&f);
        assert_eq!(decls[0], "(declare-fun bits () (_ BitVec 64))");
    }

    #[test]
    fn test_emit_declarations_array_sort() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let decls = emit_declarations(&arr);
        assert_eq!(decls[0], "(declare-fun mem () (Array (_ BitVec 64) (_ BitVec 8)))");
    }

    // --- detect_logic tests ---

    #[test]
    fn test_detect_logic_pure_int() {
        let f = Formula::Add(Box::new(int_var("x")), Box::new(Formula::Int(1)));
        assert_eq!(detect_logic(&f), "QF_LIA");
    }

    #[test]
    fn test_detect_logic_bitvector() {
        let f = Formula::BvAdd(Box::new(bv_var("a", 32)), Box::new(bv_var("b", 32)), 32);
        assert_eq!(detect_logic(&f), "QF_BV");
    }

    /// Arrays over integers, with NO uninterpreted function applied, select
    /// `QF_ALIA` — the least row that admits arrays and ints. The cascade used
    /// to answer `QF_AUFLIA` here because it had folded the UF dimension into
    /// the array arm; the lattice keeps the two apart, and `QF_ALIA` is the
    /// strictly more precise (smaller) admitting logic.
    #[test]
    fn test_detect_logic_arrays_int() {
        let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
        let f = Formula::Select(Box::new(arr), Box::new(Formula::Int(0)));
        assert_eq!(detect_logic(&f), "QF_ALIA");
    }

    /// Arrays OF bitvectors take `QF_ABV`, the name that spells exactly what
    /// the transcript uses.
    ///
    /// A previous revision answered `ALL` here, because a FULLY MONOTONE table
    /// cannot hold `QF_ALIA` and `QF_ABV` at once: `{Arrays}` is a subset of
    /// both and would have to select a name admitting no more than their
    /// intersection. Monotonicity is no longer claimed
    /// (`trust_types::logic_lattice`'s
    /// `monotonicity_fails_only_from_sets_no_row_names_exactly` says exactly
    /// where it fails), so the array and bitvector names are both selectable
    /// again and this query reaches a bitvector pipeline instead of the top of
    /// the lattice. ADMISSIBILITY — which is what this transcript needs — is
    /// unaffected: `QF_ABV` admits arrays and bitvectors, and the query uses
    /// nothing else.
    ///
    /// `{Arrays}` alone is no longer one of the violating sets, incidentally:
    /// the SMT-LIB name audit found that SMT-LIB DOES spell arrays-and-nothing-
    /// else, `QF_AX`, and added the row. That does not touch this query, which
    /// uses bitvectors too.
    /// THIS LANE BUILDS ITS OWN FEATURE RECORD, AND IT MUST CARRY THE
    /// LINEAR-FORM BIT.
    ///
    /// [`analyze_formula`] assembles `Theories` from `sort_theories` +
    /// `node_theories` + the `declare-fun` signature map — three per-node
    /// sources, none of which can decide whether an ATOM is a difference
    /// constraint. Since `QF_IDL` became a row, a record carrying `INTS` and
    /// no `WIDE_ARITH` selects `QF_IDL`, so an omission here would head EVERY
    /// integer transcript with a logic admitting only `x - y ▷◁ n`.
    ///
    /// It would also be SILENT: ay routes `QF_IDL` to its full `QfLia` solver
    /// and enforces no fragment restriction (measured 2026-09-18), so every
    /// in-house verdict would stay correct and only an external replayer would
    /// reject the evidence. Hence this test, which pins the two lanes against
    /// each other on both sides of the boundary.
    #[test]
    fn features_carry_the_linear_form_bit() {
        use trust_types::logic_lattice::{Theories, formula_theories};

        let x = || int_var("x");
        let y = || int_var("y");

        // OUT of the fragment: the bit must be charged, and the transcript
        // lane must head the GENERAL integer logic.
        let general = Formula::Gt(
            Box::new(Formula::Add(Box::new(x()), Box::new(y()))),
            Box::new(Formula::Int(3)),
        );
        assert!(
            formula_features(&general).contains(Theories::WIDE_ARITH),
            "this lane must charge the linear-form bit for a general arithmetic atom"
        );
        assert_eq!(detect_logic(&general), "QF_LIA");

        // IN the fragment: the bit must NOT be charged, and the answer is the
        // difference logic.
        let difference = Formula::Gt(
            Box::new(Formula::Sub(Box::new(x()), Box::new(y()))),
            Box::new(Formula::Int(3)),
        );
        assert!(!formula_features(&difference).contains(Theories::WIDE_ARITH));
        assert_eq!(detect_logic(&difference), "QF_IDL");

        // THE TWO LANES AGREE. `formula_theories` is trust-types' own record
        // builder; this lane's only additions are the `declare-fun` signature
        // sorts, so on a formula with no applied uninterpreted symbol the two
        // records must be EQUAL — including the linear-form bit.
        for formula in [&general, &difference] {
            assert_eq!(
                formula_features(formula),
                formula_theories(formula),
                "the transcript lane and trust-types must agree on {formula:?}"
            );
        }

        // A declared UF signature does not disturb the bit: `(f x)` is not a
        // free constant, so the atom is not a difference atom either way.
        let applied = Formula::Gt(
            Box::new(Formula::Sub(
                Box::new(Formula::FnApp { func: "f".into(), args: vec![x()], sort: Sort::Int }),
                Box::new(y()),
            )),
            Box::new(Formula::Int(3)),
        );
        let features = formula_features(&applied);
        assert!(features.contains(Theories::WIDE_ARITH) && features.contains(Theories::UF));
        assert_eq!(detect_logic(&applied), "QF_UFLIA");
    }

    #[test]
    fn test_detect_logic_arrays_bv_is_qf_abv() {
        let arr = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let f = Formula::Select(Box::new(arr), Box::new(bv_var("addr", 64)));
        assert_eq!(detect_logic(&f), "QF_ABV");
        // LEVER C, SPLIT ON MEASUREMENT 2026-09-18: the moment an `Int` joins
        // the bitvectors the pure BV name is no longer honest, and the answer
        // is `QF_AUFBVLIA` — the narrowest attested name for arrays + UF +
        // bitvectors + linear integers. THE SENTENCE THAT USED TO FOLLOW HERE
        // IS GONE because both halves of it are: it said the six SMT-LIB names
        // of the same class are on `LOGIC_LATTICE`'s rejection list "because ay
        // REFUSES them", and that `{BitVectors, Reals}` therefore stays on
        // `ALL`. Lever C made all six ROWS on 2026-09-18, so `{BitVectors,
        // Reals}` heads `QF_BVFPLRA`; and ay `9d2cda9c8727` taught the
        // in-process parser all six, re-measured 2026-09-19, so what the parser
        // accepts is no longer a reason for anything in this table.
        let mixed =
            Formula::And(vec![f, Formula::Gt(Box::new(int_var("len")), Box::new(Formula::Int(0)))]);
        assert_eq!(detect_logic(&mixed), "QF_AUFBVLIA");
    }

    #[test]
    fn test_detect_logic_quantified_int() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)))),
        );
        assert_eq!(detect_logic(&f), "LIA");
    }

    /// A quantified BITVECTOR formula takes `BV`, the SMT-LIB name for exactly
    /// that fragment. A previous revision answered `ALL` because `BV` and `LIA`
    /// would meet at "quantifiers alone", which no SMT-LIB name spells, and a
    /// monotone table cannot hold both; monotonicity is no longer claimed.
    #[test]
    fn test_detect_logic_quantified_bv_is_bv() {
        let f = Formula::Forall(
            vec![("x".into(), Sort::BitVec(32))],
            Box::new(Formula::BvULt(
                Box::new(bv_var("x", 32)),
                Box::new(Formula::BitVec { value: 100, width: 32 }),
                32,
            )),
        );
        assert_eq!(detect_logic(&f), "BV");
    }

    /// A purely propositional formula requires no theory at all, and takes the
    /// lattice BOTTOM, `QF_UF`. It used to take `QF_LIA` — harmless on its own
    /// (a Core transcript is well formed under any logic) but fatal to
    /// monotonicity: `∅ ⊆ {Floats}` while `QF_LIA` admits integers that
    /// `QF_FP` does not, so adding a feature produced a logic admitting LESS.
    /// A least element is what makes a total selector monotone at all; see note
    /// (a) on `trust_types::logic_lattice::LOGIC_LATTICE` for why `QF_UF` is
    /// recorded as admitting nothing.
    #[test]
    fn test_detect_logic_pure_bool_is_the_lattice_bottom() {
        let f = Formula::And(vec![Formula::Bool(true), Formula::Bool(false)]);
        assert_eq!(detect_logic(&f), "QF_UF");
    }

    // --- Additional bitvector operation coverage ---

    #[test]
    fn test_formula_to_smt2_bv_mul_div_rem() {
        let a = bv_var("a", 32);
        let b = bv_var("b", 32);

        assert_eq!(
            formula_to_smt2(&Formula::BvMul(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvmul a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvUDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvudiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSDiv(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvsdiv a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvURem(Box::new(a.clone()), Box::new(b.clone()), 32)),
            "(bvurem a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSRem(Box::new(a), Box::new(b), 32)), "(bvsrem a b)");
    }

    #[test]
    fn test_formula_to_smt2_bv_or_xor_shifts() {
        let a = bv_var("a", 16);
        let b = bv_var("b", 16);

        assert_eq!(
            formula_to_smt2(&Formula::BvOr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvXor(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvxor a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvShl(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvshl a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvLShr(Box::new(a.clone()), Box::new(b.clone()), 16)),
            "(bvlshr a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvAShr(Box::new(a), Box::new(b), 16)), "(bvashr a b)");
    }

    #[test]
    fn test_formula_to_smt2_bv_comparisons_all() {
        let a = bv_var("a", 8);
        let b = bv_var("b", 8);

        assert_eq!(
            formula_to_smt2(&Formula::BvULt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvult a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvULe(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvule a b)"
        );
        assert_eq!(
            formula_to_smt2(&Formula::BvSLt(Box::new(a.clone()), Box::new(b.clone()), 8)),
            "(bvslt a b)"
        );
        assert_eq!(formula_to_smt2(&Formula::BvSLe(Box::new(a), Box::new(b), 8)), "(bvsle a b)");
    }

    #[test]
    fn test_formula_to_smt2_and_or_empty_and_single() {
        // Empty And => "true", Empty Or => "false"
        assert_eq!(formula_to_smt2(&Formula::And(vec![])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![])), "false");

        // Single-element And/Or => unwrapped
        assert_eq!(formula_to_smt2(&Formula::And(vec![Formula::Bool(true)])), "true");
        assert_eq!(formula_to_smt2(&Formula::Or(vec![Formula::Bool(false)])), "false");
    }

    #[test]
    fn test_formula_to_smt2_negative_bitvec() {
        // Negative bitvector values should be rendered as two's complement
        let f = Formula::BitVec { value: -1, width: 8 };
        let smt2 = formula_to_smt2(&f);
        // -1 in 8-bit two's complement = 255
        assert_eq!(smt2, "(_ bv255 8)");
    }

    #[test]
    fn test_emit_declarations_declares_pred_symbols() {
        // `(dir_open d)` needs BOTH the arg var `d` (nullary) AND the predicate
        // symbol `dir_open` declared as `(Int) Bool` — otherwise the solver sees
        // an undeclared function (safe-api).
        let f =
            Formula::Pred(Symbol::intern("dir_open"), vec![Formula::Var("d".into(), Sort::Int)]);
        let decls = emit_declarations(&f);
        assert!(
            decls.iter().any(|d| d == "(declare-fun d () Int)"),
            "arg var must be declared: {decls:?}"
        );
        assert!(
            decls.iter().any(|d| d == "(declare-fun dir_open (Int) Bool)"),
            "predicate symbol must be declared with its arity: {decls:?}"
        );
    }

    #[test]
    fn test_emit_declarations_nullary_pred() {
        let f = Formula::Pred(Symbol::intern("priv_dropped"), vec![]);
        let decls = emit_declarations(&f);
        assert!(
            decls.iter().any(|d| d == "(declare-fun priv_dropped () Bool)"),
            "nullary predicate must be declared: {decls:?}"
        );
    }

    /// A real-valued query (a `Real`-sorted variable or a `Formula::Rat`
    /// literal) must be labelled with a Reals logic. Before this it fell into
    /// the `QF_LIA` arm — an integer question about real variables.
    #[test]
    fn real_sorted_formulas_select_a_reals_logic() {
        let x = Formula::Var("x".into(), Sort::Real);
        let half = Formula::rat("1", "2").expect("canonical");
        let pure = Formula::And(vec![
            Formula::Le(
                Box::new(Formula::Mul(Box::new(half), Box::new(x.clone()))),
                Box::new(Formula::rat_from_int(1)),
            ),
            Formula::Ge(Box::new(x.clone()), Box::new(Formula::rat_from_int(3))),
        ]);
        assert_eq!(detect_logic(&pure), "QF_LRA");
        let n = Formula::Var("n".into(), Sort::Int);
        let mixed = Formula::And(vec![
            Formula::Le(Box::new(x.clone()), Box::new(Formula::rat_from_int(1))),
            Formula::Le(Box::new(n), Box::new(Formula::Int(4))),
        ]);
        assert_eq!(detect_logic(&mixed), "QF_LIRA");
        let quantified = Formula::Forall(
            vec![(Symbol::intern("y"), Sort::Real)],
            Box::new(Formula::Le(Box::new(x.clone()), Box::new(x.clone()))),
        );
        // QUANTIFIED reals take `LRA`, the name that says exactly that. A
        // previous revision answered `LIRA` — sound, since it admits reals —
        // because a fully monotone table cannot hold both `LRA` and `LIA`.
        // Monotonicity is no longer claimed, so the precise name is back and
        // the logic line promises no integer theory the transcript does not
        // use.
        assert_eq!(detect_logic(&quantified), "LRA");
        // Declarations carry the sort through unchanged.
        let decls = emit_declarations(&pure);
        assert!(decls.iter().any(|d| d == "(declare-fun x () Real)"), "{decls:?}");
    }

    /// TRUST-04 on the TEXT lane. `emit_declarations` over the RAW formula is
    /// what the external-ay session (`IncrementalAYSession`, the compiler's
    /// solver lane) and the SMT-LIB backend send; no ay namespace applies
    /// there. The declaration it renders for a datatype lowered from a
    /// `Ty::Datatype` must be legal SMT-LIB on its own: with the raw Rust
    /// member names, `Level`'s selectors were `0`, `0`, `1`, `0` — a numeral
    /// is not a symbol (the ay binary answers `selector name must be symbol`)
    /// and a repeated selector is one symbol for several fields.
    #[test]
    fn a_lowered_datatype_declares_legal_distinct_selectors() {
        let level_ref = || Ty::Datatype { name: "Level".into(), variants: vec![] };
        let level = Sort::from_ty(&Ty::Datatype {
            name: "Level".into(),
            variants: vec![
                ("Zero".into(), vec![]),
                ("Succ".into(), vec![("0".into(), level_ref())]),
                ("Max".into(), vec![("0".into(), level_ref()), ("1".into(), level_ref())]),
                ("Param".into(), vec![("0".into(), Ty::Int { width: 64, signed: false })]),
            ],
        });
        let f = Formula::Eq(
            Box::new(Formula::Var("l".into(), level.clone())),
            Box::new(Formula::Var("m".into(), level)),
        );
        let decls = emit_declarations(&f);
        assert!(
            decls.iter().any(|d| d
                == "(declare-datatype Level ((Zero) (Succ (Succ.0 Level)) \
                    (Max (Max.0 Level) (Max.1 Level)) (Param (Param.0 (_ BitVec 64)))))"),
            "each field must be declared under its own selector symbol: {decls:?}"
        );
    }

    #[test]
    fn test_analyze_formula_fused_matches_four_walk_oracle() {
        let oracle = |formula: &Formula| -> Theories {
            let mut features = Theories::NONE;
            visit_datatype_bearing_sorts(formula, &mut |sort| {
                features.insert(trust_types::logic_lattice::sort_theories(sort));
            });
            trust_types::visit_formula_nodes(formula, &mut |node| {
                features.insert(trust_types::logic_lattice::node_theories(node));
            });
            for (_, (arg_sorts, result_sort)) in uninterpreted_symbol_signatures(formula) {
                if !arg_sorts.is_empty() {
                    features.insert(Theories::UF);
                }
                for arg_sort in &arg_sorts {
                    features.insert(trust_types::logic_lattice::sort_theories(arg_sort));
                }
                features.insert(trust_types::logic_lattice::sort_theories(&result_sort));
            }
            features.insert(trust_types::logic_lattice::wide_arithmetic_theories(formula));
            features
        };

        let samples = vec![
            Formula::Bool(false),
            Formula::BvULt(
                Box::new(Formula::Var("bv".into(), Sort::BitVec(32))),
                Box::new(Formula::BitVec { value: 7, width: 32 }),
                32,
            ),
            Formula::FpIsNaN(Box::new(Formula::Var("f".into(), Sort::Float { eb: 8, sb: 24 }))),
            Formula::Lt(
                Box::new(Formula::Sub(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(3)),
            ),
            Formula::Lt(
                Box::new(Formula::Add(
                    Box::new(Formula::Var("x".into(), Sort::Int)),
                    Box::new(Formula::Var("y".into(), Sort::Int)),
                )),
                Box::new(Formula::Int(3)),
            ),
            Formula::Eq(
                Box::new(Formula::Select(
                    Box::new(Formula::ConstArray {
                        index_sort: Sort::Bool,
                        elem_sort: Sort::Bool,
                        value: Box::new(Formula::Bool(true)),
                    }),
                    Box::new(Formula::Bool(false)),
                )),
                Box::new(Formula::Bool(true)),
            ),
            Formula::And(vec![
                Formula::IsCtor {
                    datatype: "GhostDt".into(),
                    ctor: "Some".into(),
                    arg: Box::new(Formula::Var("g".into(), Sort::Int)),
                },
                Formula::Pred(
                    Symbol::intern("p"),
                    vec![Formula::FnApp {
                        func: "k0".into(),
                        args: vec![],
                        sort: Sort::BitVec(16),
                    }],
                ),
            ]),
        ];

        for sample in &samples {
            assert_eq!(analyze_formula(sample), oracle(sample), "mismatch on {sample:?}");
            let mut streamed = String::new();
            write_declarations(sample, &mut streamed);
            let emitted = emit_declarations(sample);
            let expected =
                if emitted.is_empty() { String::new() } else { format!("{}\n", emitted.join("\n")) };
            assert_eq!(streamed, expected, "declaration mismatch on {sample:?}");
        }
    }
}
