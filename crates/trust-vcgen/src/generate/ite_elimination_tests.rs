use trust_types::{Formula, Sort};

use super::{ITE_ELIM_CASE_CAP, eliminate_term_ites};

fn v(n: &str) -> Formula {
    Formula::Var(n.to_string(), Sort::Int)
}
fn i(n: i128) -> Formula {
    Formula::Int(n)
}
fn ite(c: Formula, t: Formula, e: Formula) -> Formula {
    Formula::Ite(Box::new(c), Box::new(t), Box::new(e))
}
/// Every `Ite` in the tree is in a boolean CONDITION position, never a term.
fn no_term_ite(f: &Formula) -> bool {
    match f {
        // A term-position Ite would be a direct arg of a relation/arith op.
        Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b) => {
            !matches!(**a, Formula::Ite(..))
                && !matches!(**b, Formula::Ite(..))
                && no_term_ite(a)
                && no_term_ite(b)
        }
        Formula::Neg(a) => !matches!(**a, Formula::Ite(..)) && no_term_ite(a),
        Formula::Not(a) => no_term_ite(a),
        Formula::And(xs) | Formula::Or(xs) => xs.iter().all(no_term_ite),
        Formula::Implies(a, b) => no_term_ite(a) && no_term_ite(b),
        Formula::Ite(c, t, e) => no_term_ite(c) && no_term_ite(t) && no_term_ite(e),
        _ => true,
    }
}

#[test]
fn no_ite_formula_is_unchanged() {
    let f = Formula::And(vec![
        Formula::Ge(Box::new(v("x")), Box::new(i(0))),
        Formula::Le(Box::new(v("x")), Box::new(v("y"))),
    ]);
    assert_eq!(eliminate_term_ites(&f, ITE_ELIM_CASE_CAP), f, "no-Ite formula must be a no-op");
}

#[test]
fn eq_with_term_ite_is_lifted() {
    // `_0 == ite(c, t, e)`  ⟶  `(c → _0==t) ∧ (¬c → _0==e)`; no term-Ite remains.
    let f = Formula::Eq(
        Box::new(v("_0")),
        Box::new(ite(Formula::Gt(Box::new(v("s")), Box::new(i(100))), i(100), v("s"))),
    );
    let out = eliminate_term_ites(&f, ITE_ELIM_CASE_CAP);
    assert!(no_term_ite(&out), "result must have no term-Ite: {out:?}");
    assert!(matches!(out, Formula::And(_)), "lift produces a conjunction of guards: {out:?}");
    let dbg = format!("{out:?}");
    assert!(dbg.contains("Implies"), "guards must be Implies: {dbg}");
    assert!(dbg.contains("Eq(Var(\"_0\", Int), Int(100))"), "true branch: {dbg}");
    assert!(dbg.contains("Eq(Var(\"_0\", Int), Var(\"s\", Int))"), "false branch: {dbg}");
}

#[test]
fn ite_nested_in_arithmetic_is_lifted() {
    // `(ite(c, a, b) + 1) < n` — the Ite is buried under an Add inside a Lt.
    let f = Formula::Lt(
        Box::new(Formula::Add(
            Box::new(ite(Formula::Eq(Box::new(v("x")), Box::new(i(0))), v("a"), v("b"))),
            Box::new(i(1)),
        )),
        Box::new(v("n")),
    );
    let out = eliminate_term_ites(&f, ITE_ELIM_CASE_CAP);
    assert!(no_term_ite(&out), "nested arithmetic Ite must be fully lifted: {out:?}");
}

#[test]
fn boolean_position_ite_is_lifted() {
    // A boolean-valued Ite at formula level: `ite(c, p, q)` ⟶ `(c→p) ∧ (¬c→q)`.
    let f = ite(
        Formula::Gt(Box::new(v("x")), Box::new(i(0))),
        Formula::Ge(Box::new(v("y")), Box::new(i(1))),
        Formula::Le(Box::new(v("y")), Box::new(i(0))),
    );
    let out = eliminate_term_ites(&f, ITE_ELIM_CASE_CAP);
    assert!(no_term_ite(&out), "{out:?}");
    assert!(matches!(out, Formula::And(_)), "{out:?}");
}

#[test]
fn over_cap_fails_open_leaving_the_ite() {
    // With a tiny cap, a multi-case term is left un-lifted (fail-open) rather
    // than blowing up — verdict-preserving (backend sees today's formula).
    let f = Formula::Eq(
        Box::new(v("_0")),
        Box::new(ite(
            Formula::Gt(Box::new(v("s")), Box::new(i(100))),
            i(100),
            ite(Formula::Lt(Box::new(v("s")), Box::new(i(0))), i(0), v("s")),
        )),
    );
    // cap = 1 forces fail-open (the clamp needs 3 cases).
    let out = eliminate_term_ites(&f, 1);
    assert_eq!(out, f, "over-cap must leave the formula unchanged (fail-open)");
}
