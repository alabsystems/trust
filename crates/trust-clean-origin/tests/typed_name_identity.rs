//! Structural names must bind source lookup and sealed permissions, including
//! display collisions that the legacy string wire cannot represent.
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_clean_carrier::carrier_signature_for;
use trust_clean_origin::admission::{
    DigestMintRefusal, ExportDigestRefusal, environment_digest_for_name, mint_verdict_digest,
};
use trust_clean_origin::emit::{CleanOriginShape, plan_clean_origin_body_for_name};
use trust_clean_origin::gate::{GateRefusal, check_faithful_for_name};
use trust_symbols::{AxiomClosure, CicKernelRecheck, KernelAuthority as _, TermDigest};

fn fixture(names: &[Name]) -> (Environment, Expr, Vec<Expr>) {
    let mut env = Environment::new();
    env.init_uint_arith().unwrap();
    let uint = Expr::const_(Name::from_string("UInt64"), vec![]);
    let ty = Expr::arrow(uint.clone(), Expr::arrow(uint.clone(), uint.clone()));
    let bodies = (0..names.len())
        .map(|index| {
            Expr::lam(
                BinderInfo::Default,
                uint.clone(),
                Expr::lam(BinderInfo::Default, uint.clone(), Expr::bvar(1 - index as u32)),
            )
        })
        .collect::<Vec<_>>();
    for (name, value) in names.iter().zip(&bodies) {
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty.clone(),
            value: value.clone(),
            is_reducible: true,
        })
        .unwrap();
    }
    (env, ty, bodies)
}

#[test]
fn quoted_and_numeric_display_collisions_check_their_own_bodies() {
    for names in [
        [Name::anon().str("A").str("b"), Name::anon().str("A.b")],
        [Name::anon().str("N").num(7), Name::anon().str("N").str("7")],
    ] {
        assert_ne!(names[0], names[1]);
        assert_eq!(names[0].to_string(), names[1].to_string());
        let (env, ty, bodies) = fixture(&names);
        let signature = carrier_signature_for(&ty).unwrap();
        for (index, name) in names.iter().enumerate() {
            let plan = plan_clean_origin_body_for_name(&env, name).unwrap();
            assert_eq!(plan.declaration(), name);
            assert!(
                matches!(plan.shape(), CleanOriginShape::Projection { projected } if *projected == index)
            );
            let permission =
                check_faithful_for_name(&env, name, &bodies[index], signature.result()).unwrap();
            assert_eq!(permission.declaration(), name);
            assert!(
                check_faithful_for_name(&env, name, &bodies[1 - index], signature.result())
                    .is_err()
            );
        }
    }
}

#[test]
fn missing_structural_name_cannot_borrow_its_display_alias() {
    let qualified = Name::anon().str("A").str("b");
    let absent = Name::anon().str("A.b");
    let (env, ty, bodies) = fixture(&[qualified]);
    let signature = carrier_signature_for(&ty).unwrap();
    assert!(plan_clean_origin_body_for_name(&env, &absent).is_err());
    assert!(matches!(
        check_faithful_for_name(&env, &absent, &bodies[0], signature.result()),
        Err(GateRefusal::SideANotKernelChecked { .. })
    ));
}

#[test]
fn legacy_digest_refuses_unencodable_identity_without_relabelling_it() {
    let names = [Name::anon().str("A").str("b"), Name::anon().str("A.b")];
    let (env, ty, bodies) = fixture(&names);
    let signature = carrier_signature_for(&ty).unwrap();
    let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"typed-name-wire-control"),
        AxiomClosure::audited([]),
    );
    for (index, name) in names.iter().enumerate() {
        let faithful =
            check_faithful_for_name(&env, name, &bodies[index], signature.result()).unwrap();
        let environment = environment_digest_for_name(&env, name).unwrap();
        let result = mint_verdict_digest(&status, environment, &signature, &faithful);
        if index == 0 {
            assert!(result.is_ok());
        } else {
            let refusal = result.unwrap_err();
            assert!(matches!(refusal, DigestMintRefusal::UnencodableDeclaration { .. }));
            let export = ExportDigestRefusal::Mint(refusal);
            assert_eq!(export.decl(), name.to_string());
            assert!(!export.is_compiler_defect());
        }
    }
}
