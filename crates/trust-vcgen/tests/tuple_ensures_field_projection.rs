// Regression (over-refutation audit #2, 2026-07-04): a VALID tuple-field
// postcondition `#[ensures(|ret| ret.0 == ret.1)]` over a body returning
// `(x, x)` was FALSELY REFUTED. The contract parser now lowers `ret.0`/`ret.1`
// to `Var("_0.0")`/`Var("_0.1")`, but the return-pin only handled a SCALAR
// `_0 = <rvalue>` — a `_0 = (op0, op1)` Tuple aggregate left the fields `_0.i`
// FREE, so the negated postcondition `¬(_0.0 == _0.1)` was trivially SAT.
//
// The fix decomposes the return aggregate: each `_0.i == <field op_i>` is pinned
// under the raw `_0.i` name the postcondition uses. For `(x, x)` the VC becomes
// `_0.0 == x ∧ _0.1 == x ∧ ¬(_0.0 == _0.1)` — UNSAT, i.e. proved. The fixture is
// REAL extracted MIR (-Ztrust-dump=mir:<dir>) for `fn duplicate(x) -> (u32,u32) {(x,x)}`.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn formula_contains(formula: &Formula, pred: &impl Fn(&Formula) -> bool) -> bool {
    pred(formula) || formula.children().into_iter().any(|child| formula_contains(child, pred))
}

/// S2c versions place reads (for example `_0.0` becomes `_0.0#s0_1`).  This
/// regression checks the modeled field pins, independently of that encoding.
fn strip_versions(formula: &Formula) -> Formula {
    formula.clone().map(&mut |node| match node {
        Formula::Var(name, sort) if name.contains('#') => {
            Formula::Var(name.split('#').next().unwrap_or(&name).to_string(), sort)
        }
        other => other,
    })
}

#[test]
fn valid_tuple_field_postcondition_pins_both_return_fields() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/tuple_ensures_duplicate.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);

    let posts: Vec<&VerificationCondition> =
        vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!posts.is_empty(), "the #[ensures] clause should produce Postcondition VC(s)");

    for post in &posts {
        let formula = strip_versions(&post.formula);
        // The postcondition reasons about `_0.0` and `_0.1`.
        assert!(
            formula_contains(&formula, &|node| node.var_name() == Some("_0.0"))
                && formula_contains(&formula, &|node| node.var_name() == Some("_0.1")),
            "postcondition must reference both tuple fields `_0.0`/`_0.1`: {:?}",
            post.formula
        );
        // The FIX: each return field is pinned to its aggregate operand value
        // (here `x`), under the SAME `_0.i` projection — so the negated
        // postcondition is UNSAT (proved). A surviving free `_0.i` is exactly the
        // over-refutation. Both field pins must be present.
        assert!(
            formula_contains(&formula, &|node| {
                matches!(
                    node,
                    Formula::Eq(lhs, rhs)
                        if lhs.as_ref().var_name() == Some("_0.0")
                            && rhs.as_ref().var_name() == Some("x")
                )
            }),
            "return field `_0.0` must be pinned to its aggregate operand `x`: {:?}",
            post.formula
        );
        assert!(
            formula_contains(&formula, &|node| {
                matches!(
                    node,
                    Formula::Eq(lhs, rhs)
                        if lhs.as_ref().var_name() == Some("_0.1")
                            && rhs.as_ref().var_name() == Some("x")
                )
            }),
            "return field `_0.1` must be pinned to its aggregate operand `x`: {:?}",
            post.formula
        );
    }
}

#[test]
fn partially_lowerable_tuple_return_stays_fail_closed() {
    let mut func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/tuple_ensures_duplicate.json"))
            .expect("fixture MIR must deserialize");

    let operands = func
        .body
        .blocks
        .iter_mut()
        .flat_map(|block| block.stmts.iter_mut())
        .find_map(|stmt| match stmt {
            Statement::Assign {
                place,
                rvalue: Rvalue::Aggregate(AggregateKind::Tuple, operands),
                ..
            } if place.local == 0 && place.projections.is_empty() => Some(operands),
            _ => None,
        })
        .expect("fixture must assign the tuple return slot");
    operands[1] = Operand::Unsupported {
        kind: "adversarial-missing-sibling".to_string(),
        detail: "the second tuple projection cannot be lowered".to_string(),
    };

    let vcs = generate_vcs(&func);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "a partial `_0.0` pin must not make the unpinned `_0.1` refutable: {vcs:#?}"
    );
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, detail }
                if kind == "SpecUnverifiable"
                    && detail.contains("no conjunct pins the return slot")
        )),
        "the partially grounded postcondition must remain visibly fail-closed: {vcs:#?}"
    );
}
