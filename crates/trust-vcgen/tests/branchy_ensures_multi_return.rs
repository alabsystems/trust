// Regression (branchy #[ensures] over-refutation, 2026-07-04): a valid
// postcondition over a MULTI-RETURN body was FALSELY REFUTED. For
// `#[ensures(move |r| *r >= a)] fn branchy(a) { if a<100 { a } else { a } }` the
// return value is `a` on both branches, so `ret >= a` is trivially true — yet the
// return slot `_0` was pinned under TWO distinct SSA reaching-def tokens (bare
// `_0` from a predecessor block-def and `_0#s3_0` from the merged-token return
// read) that never unified, leaving the checked `_0` free → spurious cex.
//
// The fix runs `normalize_ssa_version_tokens` on the postcondition VC (the return
// slot is single-static-assignment, so collapsing its tokens to bare `_0` is an
// identity that CONNECTS the two pins). This test asserts the connection at the
// formula level: the Postcondition VC pins `_0` to its value AND carries NO
// disconnected `_0#<tok>` version. The fixtures are REAL extracted MIR
// (-Ztrust-dump=mir:<dir>) for the branchy function.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn valid_branchy_postcondition_is_not_falsely_refuted() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/branchy_multi_return.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);

    let posts: Vec<&VerificationCondition> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!posts.is_empty(), "the #[ensures] clause should produce Postcondition VC(s)");

    for post in &posts {
        let dbg = format!("{:?}", post.formula);
        // The return slot must be pinned to its definition (not havoc'd).
        assert!(
            dbg.contains("Eq(Var(\"_0\""),
            "postcondition must pin the return value `_0`: {dbg}"
        );
        // The FIX: no disconnected versioned return slot `_0#<tok>` may survive —
        // every occurrence must be collapsed to the bare, single-valued `_0`, so
        // the checked variable is the one bound to the return value. A surviving
        // `_0#` is exactly the misalignment that false-refuted the valid case.
        assert!(
            !dbg.contains("Var(\"_0#"),
            "return slot versions must collapse to bare `_0` (SSA identity); a \
             disconnected `_0#<tok>` reintroduces the branchy over-refutation: {dbg}"
        );
    }
}

#[test]
fn false_branchy_postcondition_still_pins_return_slot() {
    // Soundness guard (false direction): the fix must NOT make a genuinely-false
    // branchy postcondition vacuously proved. `ret > a` over `{ a }` is false
    // (ret == a). The VC must still pin `_0` to its value and negate the (false)
    // postcondition, so the obligation stays SATisfiable (refutable), not a
    // tautology. (The full `cargo test -p trust-vcgen` suite is the primary
    // false-proof guard; this pins the structural shape for the branchy case.)
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/branchy_multi_return_false.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let post = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Postcondition))
        .expect("the #[ensures] clause should produce a Postcondition VC");
    let dbg = format!("{:?}", post.formula);
    assert!(dbg.contains("Eq(Var(\"_0\""), "must pin `_0`: {dbg}");
    // The negated postcondition (`Not(Gt(_0, a))`) must be present — not folded
    // away into a vacuous truth.
    assert!(dbg.contains("Not(Gt("), "negated false postcondition must survive: {dbg}");
}

#[test]
fn valid_branchy_COMPUTED_return_is_not_falsely_refuted() {
    // `if a<100 { a+1 } else { a }` with `ensures |r| *r >= a` is VALID but was
    // falsely refuted: the return binding `__ret` is multi-assigned (not SSA), so
    // the computed arm's value (`_5.0 == a+1`, a CheckedAdd field) never reached
    // `_0`. The transitive return-pin now connects `_0` to the arm's value.
    for fixture in ["branchy_computed_return.json", "branchy_differing_return.json"] {
        let json = std::fs::read_to_string(format!("tests/fixtures/{fixture}")).unwrap();
        let func: VerifiableFunction = serde_json::from_str(&json).unwrap();
        let vcs = generate_vcs(&func);
        let posts: Vec<&VerificationCondition> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert!(!posts.is_empty(), "{fixture}: expected Postcondition VCs");
        // Every postcondition VC must pin `_0` to a CONCRETE value expression
        // (`_5.0`/`a`/`b`), i.e. `Eq(Var(_0), Var(...))` — not leave it free.
        for post in &posts {
            let dbg = format!("{:?}", post.formula);
            assert!(
                dbg.contains("Eq(Var(\"_0\", Int), Var("),
                "{fixture}: `_0` must be pinned to a concrete arm value, else it is \
                 falsely refutable: {dbg}"
            );
        }
    }
}

#[test]
fn false_branchy_computed_postcondition_still_refutes() {
    // Soundness: `if a<100 {a+1} else {a}` with `ensures |r| *r > a` is FALSE (else
    // arm ret==a, a>a is false). The transitive pin must NOT over-pin it into a
    // vacuous proof — the else-arm VC must keep `_0 == a` and negate `_0 > a`.
    let json =
        std::fs::read_to_string("tests/fixtures/branchy_computed_return_false.json").unwrap();
    let func: VerifiableFunction = serde_json::from_str(&json).unwrap();
    let vcs = generate_vcs(&func);
    let dbg: String = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect();
    // The negated (false) postcondition survives on some arm...
    assert!(dbg.contains("Not(Gt("), "negated false postcondition must survive: {dbg}");
    // ...and the else arm still binds `_0` to the bare param `a` (not the computed
    // value), so `¬(a > a)` stays SATisfiable (refutable).
    assert!(
        dbg.contains("Eq(Var(\"_0\", Int), Var(\"a\""),
        "else arm must keep `_0 == a` so the false postcondition refutes: {dbg}"
    );
}

#[test]
fn valid_early_return_ensures_binds_each_exit_value() {
    // `fn signum(x)->i32 { if x>0 {return 1} if x<0 {return -1} 0 }` with
    // `#[ensures |ret| -1<=ret<=1]` is VALID but was falsely refuted: each
    // per-exit-site postcond VC left the return slot's per-arm temp (`_5==1`,
    // `_7==-1`, `_3==0`) UNBOUND (the temps alias the `__ret` debug name and the
    // block-def dedup dropped them). The return-pin now scans the arm (not just
    // the Return block) and pins the source temp by its raw name.
    for (fixture, want_lits) in [
        ("early_return_signum.json", vec!["1", "-1", "0"]),
        ("early_return_bucket.json", vec!["0", "1", "2"]),
    ] {
        let json = std::fs::read_to_string(format!("tests/fixtures/{fixture}")).unwrap();
        let func: VerifiableFunction = serde_json::from_str(&json).unwrap();
        let vcs = generate_vcs(&func);
        let posts: Vec<&VerificationCondition> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert!(!posts.is_empty(), "{fixture}: expected Postcondition VCs");
        let all = posts.iter().map(|vc| format!("{:?}", vc.formula)).collect::<String>();
        // Every distinct return literal must be pinned to SOME temp/return slot
        // (`Eq(Var("_N", Int), Int(<lit>))`), i.e. the exit value reaches `_0`.
        for lit in want_lits {
            assert!(
                all.contains(&format!(", Int({lit}))")),
                "{fixture}: exit value {lit} must be pinned into the postcond VC: {all}"
            );
        }
    }
}

#[test]
fn false_early_return_ensures_still_refutes() {
    // Soundness: `signum` shape with `#[ensures |ret| ret >= 1]` is FALSE on the
    // -1 and 0 exit sites. The per-exit pin must bind `_L==-1` / `_L==0` so the
    // negated postcond `¬(ret>=1)` stays SATisfiable (refutable) — never vacuously
    // proved by leaving the return slot free.
    let json = std::fs::read_to_string("tests/fixtures/early_return_signum_false.json").unwrap();
    let func: VerifiableFunction = serde_json::from_str(&json).unwrap();
    let all = generate_vcs(&func)
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect::<String>();
    // The false exits are pinned to their real values (-1 and 0), so ¬(ret>=1) is SAT.
    assert!(
        all.contains(", Int(-1))"),
        "the -1 exit must be pinned (so the false ensures refutes): {all}"
    );
    assert!(all.contains(", Int(0))"), "the 0 exit must be pinned: {all}");
    assert!(
        all.contains("Ge(") && all.contains("Not("),
        "negated postcondition must survive: {all}"
    );
}
