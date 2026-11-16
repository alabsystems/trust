// Regression (plain-`BinaryOp` return value, 2026-09-17): ORDINARY Rust — a
// plain `if`/`else` whose taken arm divides — was reported `unknown` for a
// postcondition that is obviously true.
//
//     fn f(x: i32) -> i32 requires x >= 0 ensures result >= 0 {
//         if x < 0 { 0 } else { x / 2 }
//     }
//
// The emitted query named the division's temporary `_8` and never said what it
// was. With `_8` free the solver could pick `_8 = -1`, so the negated clause was
// satisfiable and the row came back `unknown` — a model of the ENCODING, never
// of the program.
//
// Two lanes had to agree for the fact to arrive:
//
//   * The transitive return pin binds `_0` to `_2`'s rvalue on this arm, which
//     is the bare local `_8`. That pin INTRODUCES `_8` into the formula long
//     after `v2_formula_with_block_defs` ran its relevance filter against a body
//     whose only free variables were `_0` and the merged `_2` token — so
//     `_8 == x / 2` had already been pruned as unrelated. The pin now re-offers
//     the block defs, the same route the deref-load return fix takes.
//   * The relevance filter compared RAW spellings, but the block def carries its
//     establish token (`_8#s5_0`) while a formula renamed at the successor block
//     carries the entry token for the same reaching def (`_8#e_s5_0`). Both
//     collapse to `_8` before the solver sees them, so the filter now compares
//     names in that post-collapse spelling.
//
// The defect was operator-shaped, which is otherwise a strange thing for a
// verifier to be: `+`, `-` and `*` lower to `CheckedBinaryOp`, whose value is a
// FIELD pinned by the arm's assert-passed semantic guard — a lane that survives
// the merge. Division, remainder and the shifts are plain `BinaryOp`, so their
// value equation exists ONLY as a block definition, which is the thing that was
// being dropped.
//
// Fixtures are REAL extracted MIR (`-Ztrust-dump=mir:<dir>`).
use trust_types::*;
use trust_vcgen::generate_vcs;

fn postcondition_formulas(fixture: &str) -> Vec<String> {
    let func: VerifiableFunction =
        serde_json::from_str(fixture).expect("fixture MIR must deserialize");
    let posts: Vec<String> = generate_vcs(&func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    assert!(!posts.is_empty(), "the `ensures` clause must produce Postcondition VC(s)");
    posts
}

/// The division's defining equation must REACH the solver. Without it the
/// temporary is free and a true postcondition is satisfiably negated.
#[test]
fn division_value_reaches_the_postcondition_query() {
    let posts = postcondition_formulas(include_str!("fixtures/div_if_else_ensures.json"));
    assert!(
        posts.iter().any(|p| p.contains("Div(Var(\"x\", Int), Int(2))")),
        "no conjunct states `x / 2`, so the return temporary is free: {posts:#?}"
    );
}

/// The temporary must be pinned under the SAME spelling the rest of the query
/// uses. A fact minted under a token nothing else mentions is a distinct SMT
/// symbol that constrains nothing — the failure mode this regression is about,
/// wearing a different mask.
#[test]
fn division_value_is_pinned_under_the_connecting_name() {
    let posts = postcondition_formulas(include_str!("fixtures/div_if_else_ensures.json"));
    let arm = posts
        .iter()
        .find(|p| p.contains("Div(Var(\"x\", Int), Int(2))"))
        .expect("the dividing arm's postcondition row");
    assert!(
        arm.contains("Eq(Var(\"_8\", Int), Div(Var(\"x\", Int), Int(2)))"),
        "the division must be stated about the bare `_8` the return pin names: {arm}"
    );
    assert!(
        arm.contains("Eq(Var(\"_0\", Int), Var(\"_8\", Int))"),
        "the return slot must be tied to that same `_8`: {arm}"
    );
}

/// Soundness guard, the direction that matters. `ensures result >= 1` over the
/// same body is FALSE (`f(0) == 0`), and adding true facts must not make it
/// vacuously provable. The row must still state the division AND still negate
/// the clause, so the query stays refutable.
#[test]
fn a_false_postcondition_over_the_same_body_stays_refutable() {
    let posts = postcondition_formulas(include_str!("fixtures/div_if_else_ensures_false.json"));
    assert!(
        posts.iter().any(|p| p.contains("Div(Var(\"x\", Int), Int(2))")),
        "the false case must reach the solver with the same facts: {posts:#?}"
    );
    assert!(
        posts.iter().any(|p| p.contains("Not(Ge(Var(\"_0\", Int), Int(1)))")),
        "the negated clause must survive, or the row proves nothing: {posts:#?}"
    );
}
