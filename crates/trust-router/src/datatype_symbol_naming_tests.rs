// trust-router/datatype_symbol_naming_tests.rs: datatype member naming is
// injective at the ay boundary (TRUST-04, TRUST-05).
//
// An SMT-LIB datatype declaration introduces GLOBAL function symbols: one per
// constructor, one per selector, one tester per constructor. Measured on the
// unfixed code, every shape below in which two distinct source entities reached
// ay under one spelling was REFUSED, i.e. declined to `Unknown`: by ay
// (reserved-name, rebinding, overloading, assertion-source and selector-sort
// errors) or, first, by the router's own datatype-term gate. Refusal is the
// fail-closed outcome; the hazard it guards is a consumer that CONFLATES the two
// into one function instead, where a conflated selector turns a satisfiable
// violation formula UNSAT, a false PROVE. The tests therefore require both the
// verdict the distinct symbols earn and, where it matters, that it is not a
// PROVE.
//
// Every test here is phrased against the SHAPES THE PIPELINE PRODUCES, not
// against a hand-picked spelling of the fix:
//
// * the kernel `Level` datatype is lowered with `Sort::from_ty` from the
//   `Ty::Datatype` trust-mir-extract emits (raw Rust member names, so every
//   tuple-variant field is `0`/`1`), and each selector is looked up in the
//   declaration that lowering produced, exactly as trust-vcgen's builders do;
// * the TRUST-05 shapes are raw user spellings (`default`, `__trust_u_kind`)
//   handed to the router, which alone owns the ay namespace.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_types::{Formula, Sort, SortFromTy, Symbol, Ty, VerificationResult};

use super::{InProcessAyBackend, execute_direct, problem_smt2};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}

fn bv64(value: i128) -> Formula {
    Formula::BitVec { value, width: 64 }
}

/// The kernel universe `Level` exactly as `lower_adt_as_datatype` extracts
/// it: five constructors, by-name `Level` self-references, and the raw Rust
/// member names — so `Succ`, `Max`, `IMax` and `Param` all call their first
/// field `0`. `Param`'s payload is a `u64` here (the real one is an opaque
/// `Name`, which has no definition to declare).
fn level_ty() -> Ty {
    level_ty_named("Level")
}

/// [`level_ty`] under the datatype name `name` — trust-mir-extract names a
/// lowered datatype by its def path (`clean_kernel::level::Level`).
fn level_ty_named(name: &str) -> Ty {
    let level_ref = || Ty::Datatype { name: name.into(), variants: vec![] };
    Ty::Datatype {
        name: name.into(),
        variants: vec![
            ("Zero".into(), vec![]),
            ("Succ".into(), vec![("0".into(), level_ref())]),
            ("Max".into(), vec![("0".into(), level_ref()), ("1".into(), level_ref())]),
            ("IMax".into(), vec![("0".into(), level_ref()), ("1".into(), level_ref())]),
            ("Param".into(), vec![("0".into(), Ty::Int { width: 64, signed: false })]),
        ],
    }
}

/// The SMT declaration the pipeline gives `Level` (`Sort::from_ty`, the one
/// Ty -> Sort lowering every trust-vcgen lane goes through).
fn level() -> Sort {
    Sort::from_ty(&level_ty())
}

fn datatype_name(sort: &Sort) -> String {
    let Sort::Datatype { name, .. } = sort else {
        panic!("expected a datatype sort, got {sort:?}")
    };
    name.clone()
}

/// The `(selector, field sort)` the declaration `sort` gives field `index` of
/// constructor `ctor` — read off the declaration, never spelled by the test.
fn declared_field(sort: &Sort, ctor: &str, index: usize) -> (String, Sort) {
    let Sort::Datatype { constructors, .. } = sort else {
        panic!("expected a datatype sort, got {sort:?}")
    };
    let (_, fields) = constructors
        .iter()
        .find(|(name, _)| name == ctor)
        .unwrap_or_else(|| panic!("constructor `{ctor}` missing from {sort:?}"));
    fields[index].clone()
}

/// `(ctor.index arg)`, spelled the way the declaration spells it.
fn sel(sort: &Sort, ctor: &str, index: usize, arg: Formula) -> Formula {
    let (field, field_sort) = declared_field(sort, ctor, index);
    Formula::Sel { datatype: datatype_name(sort), field, field_sort, arg: b(arg) }
}

fn ctor(sort: &Sort, name: &str, args: Vec<Formula>) -> Formula {
    Formula::Ctor { ctor: name.into(), args, sort: sort.clone() }
}

fn is(sort: &Sort, name: &str, arg: Formula) -> Formula {
    Formula::IsCtor { datatype: datatype_name(sort), ctor: name.into(), arg: b(arg) }
}

fn var(name: &str, sort: &Sort) -> Formula {
    Formula::Var(name.into(), sort.clone())
}

fn assert_proved(result: &VerificationResult, what: &str) {
    assert!(
        matches!(result, VerificationResult::Proved { .. }),
        "{what}: expected Proved, got {result:?}"
    );
}

/// An UNSAT whose refutation takes a selector of a constructor, `(fld (C a))
/// = a`, as a step. It is `Proved` on every build that claims no external
/// Carcara check (`trustc`'s among them). A `carcara-crosscheck` build claims
/// one, and ay renders that step as `:rule hole` (pinned Alethe has no
/// datatype rule), which the cross-check refuses before Carcara runs: the row
/// is downgraded fail-closed. The carcara arm pins both the downgrade and the
/// hole that causes it, since the downgrade's reason string alone would also
/// fit a named rule Carcara rejected. The issue is
/// docs/issues/2026-10-01-ay-alethe-hole-rule-blocks-carcara-for-datatype-and-skolem-refl.md;
/// once ay prints a rule Carcara checks there, delete the carcara arm.
fn assert_selector_unsat_proved(backend: &InProcessAyBackend, formula: &Formula, what: &str) {
    let result = backend.run(formula);
    #[cfg(not(feature = "carcara-crosscheck"))]
    assert_proved(&result, what);
    #[cfg(feature = "carcara-crosscheck")]
    {
        // MEASURED 2026-10-10 at ay `ffaba97f6` (pin train P4a.1): ay now DISCLOSES the
        // datatype-selector step as `carcara_surface=unsupported(...)` (D7) instead of
        // emitting a `:rule hole`, so the cross-check refuses BEFORE Carcara runs. Either
        // refusal is the same fail-closed downgrade; each is pinned to its own cause.
        let reason = match &result {
            VerificationResult::Unknown { reason, .. } => reason.clone(),
            other => panic!(
                "{what}: a Carcara-claiming build must refuse ay's datatype-selector step; \
                 if ay now prints a checkable rule, delete this arm. Got {other:?}"
            ),
        };
        assert!(reason.contains("fail-closed"), "{what}: not a fail-closed downgrade: {reason}");
        if reason.contains(
            "carcara N-version cross-check refused: ay disclosed carcara_surface=unsupported(",
        ) {
            assert!(
                reason.contains("datatype selector"),
                "{what}: ay disclosed an unsupported Carcara surface for some OTHER step; \
                 re-measure: {reason}"
            );
        } else {
            assert!(
                reason.contains("carcara N-version cross-check rejected"),
                "{what}: the refusal must be the Carcara cross-check's fail-closed downgrade: \
                 {reason}"
            );
            let holes = super::native_unsat_hole_steps(backend, formula);
            assert!(
                !holes.is_empty(),
                "{what}: the cross-check refused the document, but it no longer carries a \
                 `:rule hole` step, so the refusal is something else (a named rule Carcara \
                 rejects would be a real N-version disagreement). Re-measure before deleting \
                 or re-pinning this arm."
            );
        }
    }
}

/// A SAT violation must come back refuted, with a witness that names only
/// SOURCE spellings.
fn assert_refuted(result: &VerificationResult, what: &str) {
    match result {
        VerificationResult::Failed { counterexample: Some(cex), .. } => {
            for (name, _) in &cex.assignments {
                assert!(
                    !name.starts_with("__trust_"),
                    "{what}: a namespaced spelling leaked into the witness: {name}"
                );
            }
        }
        other => panic!("{what}: expected a refutation with a witness, got {other:?}"),
    }
}

/// The witness value `result` binds to `name`, rendered.
fn witness(result: &VerificationResult, name: &str) -> String {
    let VerificationResult::Failed { counterexample: Some(cex), .. } = result else {
        panic!("expected a refutation with a witness, got {result:?}")
    };
    let (_, value) = cex
        .assignments
        .iter()
        .find(|(bound, _)| bound == name)
        .unwrap_or_else(|| panic!("the witness binds no `{name}`: {:?}", cex.assignments));
    match value {
        trust_types::CounterexampleValue::Term(term) => term.clone(),
        other => format!("{other:?}"),
    }
}

/// An UNSAT query whose refutation needs a datatype lemma ay's STRICT proof
/// checker cannot certify yet (measured on the pinned ay: acyclicity and
/// tester exclusivity come back `(incomplete self-check-rejected)`, i.e. ay
/// DECIDED the query and its own proof gate withheld the verdict). What this
/// file can require of it is what naming controls: the query reaches ay's
/// decision procedure instead of being refused on the way in
/// (`in-process ay declined: …` / `in-process ay execution error: …`), ay
/// decides it (the only Unknown accepted is that proof-gate withholding, not a
/// timeout or any other undecided outcome), and it is never REFUTED (a
/// refutation of an UNSAT formula would be unsound). `Proved` is accepted, so
/// a later ay that certifies the lemma still passes.
fn assert_decided_unsat(result: &VerificationResult, what: &str) {
    match result {
        VerificationResult::Proved { .. } => {}
        VerificationResult::Unknown { reason, .. }
            if reason.starts_with("in-process ay returned unknown")
                && reason.contains("self-check-rejected") => {}
        other => panic!("{what}: expected ay to decide the UNSAT query, got {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TRUST-04 — member naming inside one datatype, and across datatypes
// ─────────────────────────────────────────────────────────────────────────────

/// A VC that merely MENTIONS a `Level`-sorted value must still be decided on
/// its own merits. Here the contradiction is pure integer arithmetic; the
/// `Level` variable only forces the datatype to be declared.
///
/// A GUARD, not a failing-first test: measured on the unfixed base, ay
/// ACCEPTED the declaration with four selectors spelled `0` and this was
/// already Proved — the defect only surfaced once a selector was applied
/// (see the tests below). It pins that the member-collision gate added with
/// the fix does not decline the declaration `Sort::from_ty` now produces.
#[test]
fn a_vc_mentioning_a_level_value_is_decided() {
    if !execute_direct::is_available() {
        return;
    }
    let level = level();
    let x = Formula::Var("x".into(), Sort::Int);
    let formula = Formula::And(vec![
        Formula::Gt(b(x.clone()), b(Formula::Int(0))),
        Formula::Lt(b(x), b(Formula::Int(0))),
        Formula::Eq(b(var("l", &level)), b(var("m", &level))),
    ]);
    assert_proved(&InProcessAyBackend::new().run(&formula), "x > 0 && x < 0 over a Level context");
}

/// `(l as Param).0` must select `Param`'s payload. With raw member names the
/// selector `0` is ALSO `Succ`'s (a `Level`), so the `u64`-sorted read was
/// refused as a sort mismatch and the obligation declined.
#[test]
fn the_param_payload_is_read_by_its_own_selector() {
    if !execute_direct::is_available() {
        return;
    }
    let level = level();
    let l = var("l", &level);
    // l = Param(7) && !(l.Param.0 == 7): UNSAT.
    let formula = Formula::And(vec![
        Formula::Eq(b(l.clone()), b(ctor(&level, "Param", vec![bv64(7)]))),
        Formula::Not(b(Formula::Eq(b(sel(&level, "Param", 0, l)), b(bv64(7))))),
    ]);
    assert_selector_unsat_proved(&InProcessAyBackend::new(), &formula, "Param payload read");
}

/// `(l as Succ).0` selects `Succ`'s own payload, a `Level`. With raw member
/// names ay resolved the selector `0` to a different constructor's field and
/// refused the read as a sort mismatch. The witness also comes back in SOURCE
/// spelling (`(Succ Zero)`), not as the namespaced constructor images ay
/// reports.
#[test]
fn the_succ_payload_is_read_by_its_own_selector() {
    if !execute_direct::is_available() {
        return;
    }
    let level = level();
    let (l, m) = (var("l", &level), var("m", &level));
    // is-Succ(l) && l.Succ.0 = m && is-Zero(m): SAT, l = Succ(Zero).
    let formula = Formula::And(vec![
        is(&level, "Succ", l.clone()),
        Formula::Eq(b(sel(&level, "Succ", 0, l)), b(m.clone())),
        is(&level, "Zero", m),
    ]);
    let result = InProcessAyBackend::new().run(&formula);
    assert_refuted(&result, "Succ payload read");
    assert_eq!(witness(&result, "l"), "(Succ Zero)");
    assert_eq!(witness(&result, "m"), "Zero");
}

/// The spelling production actually hands the router: trust-mir-extract names
/// the kernel `Level` by its def path, which is not an SMT-LIB simple symbol
/// (`::`). Its ay image is one (`::` is `$`-escaped), so ay's native
/// declaration, every term, and the transcript all name the datatype the same
/// way with no `|…|` quoting anywhere, and both payload reads behave exactly as
/// they do for the plain name `Level`.
#[test]
fn a_def_path_datatype_name_is_decided_like_a_plain_one() {
    if !execute_direct::is_available() {
        return;
    }
    let level = Sort::from_ty(&level_ty_named("clean_kernel::level::Level"));
    let backend = InProcessAyBackend::new();
    let (l, m) = (var("l", &level), var("m", &level));

    // l = Param(7) && !(l.Param.0 == 7): UNSAT.
    let unsat = Formula::And(vec![
        Formula::Eq(b(l.clone()), b(ctor(&level, "Param", vec![bv64(7)]))),
        Formula::Not(b(Formula::Eq(b(sel(&level, "Param", 0, l.clone())), b(bv64(7))))),
    ]);
    assert_selector_unsat_proved(&backend, &unsat, "def-path Level, Param payload read");
    let transcript = problem_smt2(&unsat);
    assert!(
        !transcript.contains('|'),
        "every symbol of the transcript must be a simple symbol, so the datatype is spelled \
         the same in its declaration and in every term:\n{transcript}"
    );

    // is-Succ(l) && l.Succ.0 = m && is-Zero(m): SAT, l = Succ(Zero).
    let sat = Formula::And(vec![
        is(&level, "Succ", l.clone()),
        Formula::Eq(b(sel(&level, "Succ", 0, l)), b(m.clone())),
        is(&level, "Zero", m),
    ]);
    let result = backend.run(&sat);
    assert_refuted(&result, "def-path Level, Succ payload read");
    assert_eq!(witness(&result, "l"), "(Succ Zero)");
}

/// Acyclicity through `Succ`'s own selector: `l = Succ(l)` has no model in the
/// term algebra. With raw member names the query was refused before ay ran
/// (selector sort mismatch); now ay decides it — see [`assert_decided_unsat`]
/// for why `Proved` is not yet required.
#[test]
fn succ_acyclicity_reaches_the_decision_procedure() {
    if !execute_direct::is_available() {
        return;
    }
    let level = level();
    let l = var("l", &level);
    let formula = Formula::And(vec![
        is(&level, "Succ", l.clone()),
        Formula::Eq(b(sel(&level, "Succ", 0, l.clone())), b(l)),
    ]);
    assert_decided_unsat(&InProcessAyBackend::new().run(&formula), "Succ acyclicity");
}

/// THE SOUNDNESS SHAPE. `Max.0` and `IMax.0` are two different functions:
/// applied to a `Max` value, `IMax.0` is unconstrained, so
/// `l = Max(a, b) && l.Max.0 != l.IMax.0` is SATISFIABLE. Were the two
/// selectors ever spelled alike, the formula would read `t != t` for one
/// term `t` — UNSAT, a false PROVE. The only acceptable verdict is a
/// refutation.
#[test]
fn same_position_fields_of_two_constructors_are_not_conflated() {
    if !execute_direct::is_available() {
        return;
    }
    let level = level();
    let l = var("l", &level);
    let formula = Formula::And(vec![
        Formula::Eq(b(l.clone()), b(ctor(&level, "Max", vec![var("a", &level), var("b", &level)]))),
        Formula::Not(b(Formula::Eq(
            b(sel(&level, "Max", 0, l.clone())),
            b(sel(&level, "IMax", 0, l)),
        ))),
    ]);
    let result = InProcessAyBackend::new().run(&formula);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "Max.0 and IMax.0 were conflated into one symbol: a satisfiable formula was PROVED"
    );
    assert_refuted(&result, "Max.0 vs IMax.0");
}

/// `Lvl = Zero | Max(Lvl, Lvl) | IMax(Lvl, Lvl)` — the `Level` shape minus
/// `Param`, so every tuple field has the SAME sort and a selector spelled `0`
/// raises no sort mismatch anywhere.
fn max_imax_ty() -> Ty {
    let lvl_ref = || Ty::Datatype { name: "Lvl".into(), variants: vec![] };
    Ty::Datatype {
        name: "Lvl".into(),
        variants: vec![
            ("Zero".into(), vec![]),
            ("Max".into(), vec![("0".into(), lvl_ref()), ("1".into(), lvl_ref())]),
            ("IMax".into(), vec![("0".into(), lvl_ref()), ("1".into(), lvl_ref())]),
        ],
    }
}

/// The same conflation hazard with every colliding field at ONE sort, so no
/// Trust-side sort gate can object (measured: on the unfixed base the pinned
/// ay still refused the read with its own selector sort check, so this failed
/// closed rather than proving). The formula is SATISFIABLE (`IMax.0` of a
/// `Max` value is unconstrained); it must be refuted, and above all never
/// PROVED.
#[test]
fn same_sorted_fields_of_two_constructors_are_not_conflated() {
    if !execute_direct::is_available() {
        return;
    }
    let lvl = Sort::from_ty(&max_imax_ty());
    let l = var("l", &lvl);
    let formula = Formula::And(vec![
        Formula::Eq(b(l.clone()), b(ctor(&lvl, "Max", vec![var("a", &lvl), var("b", &lvl)]))),
        Formula::Not(b(Formula::Eq(b(sel(&lvl, "Max", 0, l.clone())), b(sel(&lvl, "IMax", 0, l))))),
    ]);
    let result = InProcessAyBackend::new().run(&formula);
    assert!(
        !matches!(result, VerificationResult::Proved { .. }),
        "Max.0 and IMax.0 were conflated into one symbol: a satisfiable formula was PROVED \
         ({result:?})"
    );
    assert_refuted(&result, "same-sorted Max.0 vs IMax.0");
}

/// Two datatypes each with a constructor `Var` and a selector `v` — a shape
/// any two Rust enums produce. Constructors and selectors are global symbols,
/// so without datatype qualification the second declaration re-declares the
/// first one's `Var` and `v`.
fn term_and_pat(pat_payload: Sort) -> (Sort, Sort) {
    let term_ref = Sort::Datatype { name: "Term".into(), constructors: vec![] };
    let term = Sort::Datatype {
        name: "Term".into(),
        constructors: vec![
            ("Var".into(), vec![("v".into(), Sort::Int)]),
            ("App".into(), vec![("f".into(), term_ref.clone()), ("x".into(), term_ref)]),
        ],
    };
    let pat = Sort::Datatype {
        name: "Pat".into(),
        constructors: vec![
            ("Var".into(), vec![("v".into(), pat_payload)]),
            ("Wild".into(), vec![]),
        ],
    };
    (term, pat)
}

#[test]
fn two_datatypes_sharing_a_constructor_and_a_selector_name_are_both_decided() {
    if !execute_direct::is_available() {
        return;
    }
    let backend = InProcessAyBackend::new();

    // The shared selector `v` is an Int in both datatypes, then an Int in one
    // and a Bool in the other. Either way both declarations must coexist in
    // one query: t = Term.Var(1) && p = Pat.Var(..) && !(t.v = 1) is UNSAT.
    for (pat_payload, pat_value) in
        [(Sort::Int, Formula::Int(2)), (Sort::Bool, Formula::Bool(true))]
    {
        let (term, pat) = term_and_pat(pat_payload.clone());
        let (t, p) = (var("t", &term), var("p", &pat));
        let unsat = Formula::And(vec![
            Formula::Eq(b(t.clone()), b(ctor(&term, "Var", vec![Formula::Int(1)]))),
            Formula::Eq(b(p), b(ctor(&pat, "Var", vec![pat_value]))),
            Formula::Not(b(Formula::Eq(b(sel(&term, "Var", 0, t)), b(Formula::Int(1))))),
        ]);
        assert_selector_unsat_proved(
            &backend,
            &unsat,
            &format!("shared Var/v, Pat payload {pat_payload:?}"),
        );
    }

    // SAT, reading BOTH `v`s: is-Var(t) && is-Var(p) && t.v = p.v + 1. The
    // witness names each value by its source constructor.
    let (term, pat) = term_and_pat(Sort::Int);
    let (t, p) = (var("t", &term), var("p", &pat));
    let sat = Formula::And(vec![
        is(&term, "Var", t.clone()),
        is(&pat, "Var", p.clone()),
        Formula::Eq(
            b(sel(&term, "Var", 0, t)),
            b(Formula::Add(b(sel(&pat, "Var", 0, p)), b(Formula::Int(1)))),
        ),
    ]);
    let result = backend.run(&sat);
    assert_refuted(&result, "shared Var/v, SAT");
    assert!(witness(&result, "t").starts_with("(Var "), "{result:?}");
    assert!(witness(&result, "p").starts_with("(Var "), "{result:?}");
}

/// Parse one SMT-LIB s-expression list (enough for a transcript line):
/// `(`/`)` delimit, `|…|` is one symbol, whitespace separates.
#[derive(Debug, Clone)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn parse_sexp(text: &str) -> Sexp {
    fn parse(chars: &[char], pos: &mut usize) -> Sexp {
        while chars[*pos].is_whitespace() {
            *pos += 1;
        }
        if chars[*pos] == '(' {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                while chars[*pos].is_whitespace() {
                    *pos += 1;
                }
                if chars[*pos] == ')' {
                    *pos += 1;
                    return Sexp::List(items);
                }
                items.push(parse(chars, pos));
            }
        }
        let mut atom = String::new();
        if chars[*pos] == '|' {
            atom.push('|');
            *pos += 1;
            while chars[*pos] != '|' {
                atom.push(chars[*pos]);
                *pos += 1;
            }
            atom.push('|');
            *pos += 1;
            return Sexp::Atom(atom);
        }
        while *pos < chars.len() && !chars[*pos].is_whitespace() && !"()".contains(chars[*pos]) {
            atom.push(chars[*pos]);
            *pos += 1;
        }
        Sexp::Atom(atom)
    }
    let chars: Vec<char> = text.chars().collect();
    parse(&chars, &mut 0)
}

fn atom(sexp: &Sexp) -> &str {
    match sexp {
        Sexp::Atom(atom) => atom,
        Sexp::List(items) => panic!("expected an atom, got {items:?}"),
    }
}

/// Every function symbol the transcript's `(declare-datatype …)` lines
/// introduce — constructors and selectors — with how many times each is
/// declared, keyed by `(datatype, constructor)` for the constructor that
/// declares it.
fn declared_datatype_symbols(transcript: &str) -> BTreeMap<String, Vec<(String, String)>> {
    let mut symbols: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for line in transcript.lines().filter(|line| line.starts_with("(declare-datatype ")) {
        let Sexp::List(items) = parse_sexp(line) else { panic!("not a list: {line}") };
        let datatype = atom(&items[1]).to_string();
        let Sexp::List(constructors) = &items[2] else { panic!("no constructor list: {line}") };
        for constructor in constructors {
            let Sexp::List(parts) = constructor else { panic!("bad constructor in {line}") };
            let ctor = atom(&parts[0]).to_string();
            symbols.entry(ctor.clone()).or_default().push((datatype.clone(), ctor.clone()));
            for selector in &parts[1..] {
                let Sexp::List(pair) = selector else { panic!("bad selector in {line}") };
                symbols
                    .entry(atom(&pair[0]).to_string())
                    .or_default()
                    .push((datatype.clone(), ctor.clone()));
            }
        }
    }
    symbols
}

/// The transcript is evidence (the revalidation digest and the Carcara
/// cross-check are taken over it), so it must be a declaration a solver can
/// accept: every constructor and selector of every datatype it declares is
/// declared exactly once, and the two `Param`/`Succ` payload selectors are
/// different symbols.
#[test]
fn the_transcript_declares_every_datatype_member_exactly_once() {
    let level = level();
    let (term, pat) = term_and_pat(Sort::Int);
    let l = var("l", &level);
    let formula = Formula::And(vec![
        Formula::Eq(b(sel(&level, "Param", 0, l.clone())), b(bv64(7))),
        is(&level, "Succ", l),
        Formula::Eq(b(var("t", &term)), b(var("t2", &term))),
        Formula::Eq(b(var("p", &pat)), b(var("p2", &pat))),
    ]);
    let transcript = problem_smt2(&formula);
    let symbols = declared_datatype_symbols(&transcript);
    // Level: 5 constructors + 6 selectors; Term: 2 + 3; Pat: 2 + 1.
    assert_eq!(
        symbols.values().map(Vec::len).sum::<usize>(),
        (5 + 6) + (2 + 3) + (2 + 1),
        "expected every Level, Term and Pat member to be declared:\n{transcript}"
    );
    let duplicated: Vec<_> = symbols.iter().filter(|(_, owners)| owners.len() > 1).collect();
    assert!(
        duplicated.is_empty(),
        "one symbol declared by several datatype members: {duplicated:?}\n{transcript}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// TRUST-05 — the datatype family and the uninterpreted symbols share the
// namespace discipline the variables already have
// ─────────────────────────────────────────────────────────────────────────────

/// A Rust field named `default` (an ay array builtin). Variables spelled like
/// a builtin were namespaced by 439720e01b; a datatype MEMBER spelled like one
/// still declined with `symbol 'default' is a reserved ay builtin`.
#[test]
fn a_datatype_member_spelled_like_an_ay_builtin_reaches_a_verdict() {
    if !execute_direct::is_available() {
        return;
    }
    let config = Sort::Datatype {
        name: "Config".into(),
        constructors: vec![("Config".into(), vec![("default".into(), Sort::Int)])],
    };
    let c = var("c", &config);
    let backend = InProcessAyBackend::new();

    let unsat = Formula::And(vec![
        Formula::Eq(b(c.clone()), b(ctor(&config, "Config", vec![Formula::Int(5)]))),
        Formula::Not(b(Formula::Eq(b(sel(&config, "Config", 0, c.clone())), b(Formula::Int(5))))),
    ]);
    assert_selector_unsat_proved(&backend, &unsat, "field `default`, UNSAT");

    let sat = Formula::Gt(b(sel(&config, "Config", 0, c)), b(Formula::Int(3)));
    assert_refuted(&backend.run(&sat), "field `default`, SAT");

    // Every member class at once: a datatype, a constructor and a selector
    // each spelled like an ay builtin.
    let fp = Sort::Datatype {
        name: "fp".into(),
        constructors: vec![
            ("concat".into(), vec![("select".into(), Sort::Int)]),
            ("store".into(), vec![]),
        ],
    };
    let x = var("x", &fp);
    let unsat = Formula::And(vec![
        Formula::Eq(b(x.clone()), b(ctor(&fp, "concat", vec![Formula::Int(5)]))),
        Formula::Not(b(Formula::Eq(b(sel(&fp, "concat", 0, x.clone())), b(Formula::Int(5))))),
    ]);
    assert_selector_unsat_proved(&backend, &unsat, "builtin-named datatype family, UNSAT");
    let sat = Formula::And(vec![
        is(&fp, "concat", x.clone()),
        Formula::Gt(b(sel(&fp, "concat", 0, x)), b(Formula::Int(0))),
    ]);
    let result = backend.run(&sat);
    assert_refuted(&result, "builtin-named datatype family, SAT");
    assert!(witness(&result, "x").starts_with("(concat "), "{result:?}");
}

/// A field literally named `__trust_u_kind` next to a local `kind`. The local
/// is namespaced to `__trust_u_kind`; an un-namespaced selector with that
/// exact spelling then collides with it (ay: "already bound to a different
/// declaration"), so the query declined.
#[test]
fn a_datatype_member_spelled_like_a_namespaced_variable_does_not_alias_it() {
    if !execute_direct::is_available() {
        return;
    }
    let expr = Sort::Datatype {
        name: "Expr".into(),
        constructors: vec![("Expr".into(), vec![("__trust_u_kind".into(), Sort::Int)])],
    };
    let e_kind = sel(&expr, "Expr", 0, var("e", &expr));
    let kind = Formula::Var("kind".into(), Sort::Int);
    let backend = InProcessAyBackend::new();

    let unsat = Formula::And(vec![
        Formula::Eq(b(e_kind.clone()), b(kind.clone())),
        Formula::Not(b(Formula::Eq(b(e_kind.clone()), b(kind.clone())))),
    ]);
    assert_proved(&backend.run(&unsat), "selector `__trust_u_kind` beside local `kind`, UNSAT");

    let sat = Formula::And(vec![
        Formula::Eq(b(e_kind), b(kind.clone())),
        Formula::Gt(b(kind), b(Formula::Int(3))),
    ]);
    let result = backend.run(&sat);
    assert_refuted(&result, "selector `__trust_u_kind` beside local `kind`, SAT");
    let VerificationResult::Failed { counterexample: Some(cex), .. } = &result else {
        unreachable!("assert_refuted checked the shape")
    };
    assert!(
        cex.assignments.iter().any(|(name, _)| name == "kind"),
        "the witness must bind the SOURCE local `kind`: {:?}",
        cex.assignments
    );
}

/// An uninterpreted FUNCTION or PREDICATE symbol spelled like a namespaced
/// variable must stay a different symbol from that variable: the variable `x`
/// is handed to ay as `__trust_u_x`, so a function literally named
/// `__trust_u_x` must not be. (Unary symbols: a NULLARY `FnApp` beside a
/// variable is refused by ay's `assert_term_with_source` whatever its name —
/// measured with `fzero = 1 && y = 2`, `source does not reconstruct the native
/// assertion` — which is a separate limitation.)
#[test]
fn an_uninterpreted_symbol_spelled_like_a_namespaced_variable_does_not_alias_it() {
    if !execute_direct::is_available() {
        return;
    }
    let backend = InProcessAyBackend::new();
    let (x, y) = (Formula::Var("x".into(), Sort::Int), Formula::Var("y".into(), Sort::Int));
    let f_y = Formula::FnApp { func: "__trust_u_x".into(), args: vec![y.clone()], sort: Sort::Int };

    // f(y) = 1 && x = 2: SAT.
    let sat = Formula::And(vec![
        Formula::Eq(b(f_y.clone()), b(Formula::Int(1))),
        Formula::Eq(b(x.clone()), b(Formula::Int(2))),
    ]);
    let result = backend.run(&sat);
    assert_refuted(&result, "FnApp `__trust_u_x` beside variable `x`, SAT");
    assert_eq!(witness(&result, "x"), "Int(2)");

    // f(y) = 1 && x = 2 && f(y) = x: UNSAT.
    let unsat = Formula::And(vec![
        Formula::Eq(b(f_y.clone()), b(Formula::Int(1))),
        Formula::Eq(b(x.clone()), b(Formula::Int(2))),
        Formula::Eq(b(f_y), b(x)),
    ]);
    assert_proved(&backend.run(&unsat), "FnApp `__trust_u_x` beside variable `x`, UNSAT");

    // p(y) && !flag: SAT.
    let p_y = Formula::Pred(Symbol::intern("__trust_u_flag"), vec![y]);
    let flag = Formula::Var("flag".into(), Sort::Bool);
    let result = backend.run(&Formula::And(vec![p_y, Formula::Not(b(flag))]));
    assert_refuted(&result, "Pred `__trust_u_flag` beside variable `flag`");
    assert_eq!(witness(&result, "flag"), "Bool(false)");
}
