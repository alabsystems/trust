use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

#[derive(Clone, Copy)]
pub enum Mutation {
    Honest,
    MissingRequires,
    MalformedReification,
    MissingResultBinding,
}

/// Standalone transcription of the measured branch-clamp postcondition VC.
pub fn vc(mutation: Mutation) -> VerificationCondition {
    use Formula as F;

    let iv = |name: &str| F::Var(name.to_string(), Sort::Int);
    let bv = |name: &str| F::Var(name.to_string(), Sort::Bool);
    let le = |a, b| F::Le(Box::new(a), Box::new(b));
    let lt = |a, b| F::Lt(Box::new(a), Box::new(b));
    let gt = |a, b| F::Gt(Box::new(a), Box::new(b));
    let ge = |a, b| F::Ge(Box::new(a), Box::new(b));
    let eq = |a, b| F::Eq(Box::new(a), Box::new(b));
    let not = |a| F::Not(Box::new(a));
    let implies = |a, b| F::Implies(Box::new(a), Box::new(b));
    const IMAX: i128 = i128::MAX;
    const UMAX: u128 = u128::MAX;

    let arm = |second: F| {
        let reified_hi = if matches!(mutation, Mutation::MalformedReification) {
            eq(bv("_10"), F::Int(1))
        } else {
            eq(bv("_10"), gt(iv("_8"), iv("hi")))
        };
        let mut state = vec![
            F::And(vec![le(F::Int(0), iv("_6")), le(iv("_6"), F::UInt(UMAX))]),
            F::And(vec![le(F::Int(-IMAX - 1), iv("_8")), le(iv("_8"), F::Int(IMAX))]),
            eq(bv("_9"), lt(iv("_8"), iv("lo"))),
            reified_hi,
        ];
        if !matches!(mutation, Mutation::MissingResultBinding) {
            state.push(F::And(vec![
                implies(not(bv("_10")), eq(iv("_4"), iv("_8"))),
                implies(not(not(bv("_10"))), eq(iv("_4"), iv("hi"))),
            ]));
        }
        state.push(F::And(vec![
            eq(iv("_0"), iv("_4")),
            eq(iv("_5"), iv("_4")),
            F::And(vec![
                eq(iv("_0"), iv("_5")),
                F::And(vec![
                    eq(iv("_0"), iv("_5b")),
                    not(F::And(vec![le(iv("lo"), iv("_0")), le(iv("_0"), iv("hi"))])),
                ]),
            ]),
        ]));

        let mut members = vec![not(lt(iv("_8"), iv("lo"))), second];
        if !matches!(mutation, Mutation::MissingRequires) {
            members.push(le(iv("lo"), iv("hi")));
        }
        members.push(F::And(state));
        F::And(members)
    };

    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "r174_fixture::branch_clamp".into(),
        location: SourceSpan::default(),
        formula: F::And(vec![
            ge(iv("off"), F::Int(0)),
            F::Or(vec![arm(not(gt(iv("_8"), iv("hi")))), arm(gt(iv("_8"), iv("hi")))]),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}
