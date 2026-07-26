// Regression (over-refutation audit #7, 2026-07-06): a return via a `&mut`
// store-then-load was FALSELY REFUTED:
//
//   #[ensures(|r| *r == 7)]
//   fn store_load() -> u32 { let mut x = 0; let p = &mut x; *p = 7; *p }
//
// Root cause: the block-def pass correctly computes the self-consistent chain
// `x#<k> == 7` (the deref-store) and `__ret#<k'> == x#<k>` (the deref-load), but
// `v2_formula_with_block_defs` ran its relevance filter against the bare
// obligation `¬(_0 == 7)` — whose only free variable is `_0` — BEFORE the
// return-value pin reconnected `_0` to the referent version `x#<k>`. Neither def
// mentions `_0`, so both were pruned; the late pin then reintroduced `x#<k>` with
// no `x#<k> == 7` to ground it, and `¬(_0 == 7)` stayed SAT (refuted).
//
// The fix RE-conjoins the now-relevant block-defs after the return-value pins, so
// the establishing store `x#<k> == 7` survives — `¬(_0 == 7)` becomes UNSAT
// (proved). Both fixtures are REAL MIR extracted with `-Ztrust-dump=mir:<dir>`.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn postcond_debug(json: &str) -> String {
    let func: VerifiableFunction = serde_json::from_str(json).expect("fixture must deserialize");
    let dbgs: Vec<String> = generate_vcs(&func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    assert!(!dbgs.is_empty(), "the #[ensures] clause must produce a Postcondition VC");
    dbgs.join(" ")
}

#[test]
fn valid_deref_store_load_postcondition_is_provable() {
    // `*p = 7; *p` with `ensures r == 7`.
    let dbg = postcond_debug(include_str!("fixtures/store_load_deref.json"));
    // The FIX: the deref-store's establishing def `x#<k> == 7` is present (was
    // pruned as irrelevant before) AND `_0` is pinned to that same referent
    // version — so the chain `_0 == x#<k> == 7` contradicts `¬(_0 == 7)` (proved).
    assert!(
        dbg.contains("Int(7)"),
        "the deref-store's established value 7 must survive into the VC: {dbg}"
    );
    assert!(
        dbg.contains("Eq(Var(\"_0\", Int), Var(\"x#") && dbg.contains("Eq(Var(\"x#"),
        "the return slot `_0` must be pinned to the referent version, which is \
         pinned to 7 — the connected chain that makes the VC UNSAT: {dbg}"
    );
}

#[test]
fn false_deref_store_load_postcondition_stays_refutable() {
    // Same body stores 7 but claims `ensures r == 8` — MUST stay refutable.
    let dbg = postcond_debug(include_str!("fixtures/store_load_false.json"));
    // The store value is pinned to its GENUINE value 7 (never credited to 8),
    // and the negated postcondition `¬(_0 == 8)` is present — so with `_0 == 7`
    // the conjunction is SAT (refuted), never a vacuous false-PROVE.
    assert!(
        dbg.contains("Int(7)"),
        "the genuine stored value 7 must be pinned (not the claimed 8): {dbg}"
    );
    assert!(
        dbg.contains("Not(Eq(Var(\"_0\", Int), Int(8)))"),
        "the negated false postcondition must remain, keeping the VC refutable: {dbg}"
    );
}
