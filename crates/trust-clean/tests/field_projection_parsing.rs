//! Regression: the spec parser handles general field projection (`p.value`),
//! producing a synthetic variable `p.value` that matches the MIR Adt-field
//! extraction's naming. This is the parser-level enabler for closure-contract
//! decompilation of struct-field-referencing postconditions (e.g. an accessor's
//! `#[ensures(|ret| *ret == p.value)]`). The remaining step to *prove* such a
//! contract is grounding `p.value` as a typed `Prod.fst`/`Prod.snd` projection
//! of the parameter (the witness-grounding increment).

use trust_types::{Formula, Sort};

#[test]
fn parser_handles_general_field_projection() {
    let f = trust_types::parse_spec_expr("result == p.value")
        .expect("general field projection `p.value` must parse (was unsupported)");
    assert_eq!(
        f,
        Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("p.value".into(), Sort::Int)),
        )
    );
}

#[test]
fn parser_still_handles_method_calls_alongside_fields() {
    // `.len()` (parenthesized method) keeps its existing mapping; only a bare
    // `.field` (no parens) is the new field-projection path.
    let f = trust_types::parse_spec_expr("xs.len > 0").expect("field projection on len parses");
    assert_eq!(
        f,
        Formula::Gt(
            Box::new(Formula::Var("xs.len".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        )
    );
}

/// END-TO-END: a struct accessor `fn get(p: Wrapper{value:i32}) -> i32 { p.value }`
/// with `#[ensures(result == p.value)]` is PROVEN INHABITED in the real Clean
/// kernel modulo the 3 axioms. The field reference `p.value` grounds — on BOTH
/// the predicate side (`reflect_contract` rewrites it to a `Trust.Proj.0` carrier
/// → structural `Prod` projection of the bound parameter) and the witness side
/// (`ground_int_fields` maps it to the same projection) — so the postcondition
/// `ret == p.value` and the return `p.value` unify and close by `Eq.refl`.
#[test]
fn struct_accessor_contract_proven_inhabited_modulo_3() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, Statement, Terminator,
        Ty, VerifiableBody, VerifiableFunction,
    };
    let i = || Ty::Int { width: 32, signed: true };
    let wrapper = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "Wrapper".into(), fields: vec![("value".into(), i())],
        disc_index_safe: false, faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "get".into(),
        def_path: "crate::get".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: wrapper, name: Some("p".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Field(0)],
                    })),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var("p.value".into(), Sort::Int)),
        )],
        spec: Default::default(),
    };
    assert_eq!(
        trust_clean::inhabit_verifiable_function(&func),
        trust_clean::InhabitOutcome::Inhabited,
        "struct accessor `get(p) -> p.value` with `ensures ret == p.value` must be PROVEN INHABITED modulo 3"
    );
}

/// COMPARISON over a field, proved from a field PRECONDITION (the comparison-path
/// grounding): `fn floor(p: W{v:i32}) -> i32 { p.v }` with
/// `#[requires(p.v > 100)] #[ensures(|r| *r > 100)]` is PROVEN INHABITED modulo 3.
/// The return `p.v` and both the postcondition `ret > 100` and precondition
/// `p.v > 100` ground the field `p.v` to the SAME `Prod` projection (now that the
/// grounding map is unified `String → Expr`), and `prove_lt` discharges the goal
/// `100 < p.v` from the precondition hypothesis via `Int.lt_of_lt_of_le` + `le_refl`.
#[test]
fn field_comparison_contract_proven_from_field_precondition_modulo_3() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, Statement, Terminator,
        Ty, VerifiableBody, VerifiableFunction,
    };
    let i = || Ty::Int { width: 32, signed: true };
    let w = Ty::Adt { adt_kind: None, layout: None,  variants: Vec::new(), name: "W".into(), fields: vec![("v".into(), i())],
        disc_index_safe: false, faithful_enum_repr: None, enum_layout: None, };
    let pv = || Formula::Var("p.v".into(), Sort::Int);
    let func = VerifiableFunction {
        name: "floor".into(),
        def_path: "crate::floor".into(),
        span: Default::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: i(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: w, name: Some("p".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Field(0)],
                    })),
                    span: Default::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: i(),
        },
        contracts: vec![],
        preconditions: vec![Formula::Gt(Box::new(pv()), Box::new(Formula::Int(100)))],
        postconditions: vec![Formula::Gt(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Int(100)),
        )],
        spec: Default::default(),
    };
    assert_eq!(
        trust_clean::inhabit_verifiable_function(&func),
        trust_clean::InhabitOutcome::Inhabited,
        "field-comparison contract `floor(p) -> p.v requires p.v>100 ensures ret>100` must be PROVEN INHABITED modulo 3"
    );
}
