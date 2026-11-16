use trust_types::{BasicBlock, LocalDecl, SourceSpan, VerifiableBody};

use super::*;

fn subject(alias: usize, param_name: &str, alias_name: Option<&str>) -> VerifiableFunction {
    let mut func = VerifiableFunction {
        name: "carrier_copy".into(),
        def_path: "test::carrier_copy".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some(param_name.into()) },
                LocalDecl { index: alias, ty: Ty::u64(), name: alias_name.map(str::to_string) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(alias),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(alias))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let param = Formula::var(&trust_vcgen::place_to_var_name(&func, &Place::local(1)), Sort::Int);
    func.preconditions = vec![safety_rust_type_range_constraint(&param, &Ty::u64()).unwrap()];
    func.postconditions =
        vec![Formula::Le(Box::new(Formula::var("_0", Sort::Int)), Box::new(param))];
    func
}

#[test]
fn whole_copy_and_colliding_names_keep_carrier_parity() {
    for (param, alias) in [("x", Some("value")), ("x", Some("x")), ("_2", None)] {
        let func = subject(2, param, alias);
        trust_vcgen::validate_function(&func).unwrap();
        let posts: Vec<_> = trust_vcgen::generate_vcs(&func)
            .into_iter()
            .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
            .collect();
        assert_eq!(posts.len(), 1);
        let probe = Formula::Eq(
            Box::new(Formula::var("_0", Sort::Int)),
            Box::new(Formula::var(
                &trust_vcgen::place_to_var_name(&func, &Place::local(2)),
                Sort::Int,
            )),
        );
        let canonical = trust_types::conjoin_postcondition_integer_carriers(
            &func,
            probe.clone(),
            |decl| trust_vcgen::place_to_var_name(&func, &Place::local(decl.index)),
            safety_rust_type_range_constraint,
        );
        assert_eq!(canonical, conjoin_reconstructed_postcondition_carriers(&func, probe));
    }
}

#[test]
fn sparse_and_reordered_copy_locals_use_the_same_carrier_selection() {
    for alias_index in [2, 30] {
        let mut func = subject(alias_index, "x", Some("value"));
        for reorder in [false, true] {
            if reorder {
                func.body.locals.reverse();
            }
            if alias_index == 2 && !reorder {
                trust_vcgen::validate_function(&func).unwrap();
            } else {
                // These standalone naming/selection APIs stay total; production
                // continues to refuse noncanonical declaration tables.
                assert!(trust_vcgen::validate_function(&func).is_err());
            }
            let value = trust_vcgen::place_to_var_name(&func, &Place::local(alias_index));
            assert_ne!(
                value,
                trust_vcgen::place_to_var_name(&func, &Place::local(1)),
                "whole integer copy keeps its identity"
            );
            let probe = Formula::Eq(
                Box::new(Formula::var("_0", Sort::Int)),
                Box::new(Formula::var(&value, Sort::Int)),
            );
            let canonical = trust_types::conjoin_postcondition_integer_carriers(
                &func,
                probe.clone(),
                |decl| trust_vcgen::place_to_var_name(&func, &Place::local(decl.index)),
                safety_rust_type_range_constraint,
            );
            let spine = trust_types::conjoin_postcondition_integer_carriers(
                &func,
                probe,
                |decl| collision_safe_local_name(&func.body.locals, decl.index),
                safety_rust_type_range_constraint,
            );
            assert_eq!(canonical, spine, "alias={alias_index} reordered={reorder}");
        }
    }
}
