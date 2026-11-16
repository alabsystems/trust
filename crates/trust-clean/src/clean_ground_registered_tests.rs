//! Registration-to-contract transport controls. These test the real registration
//! boundary, not a claim of Rust source/model refinement.

use trust_types::{Ty, VariantDef};

use super::*;

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

fn wrapper(field: Ty) -> reflect::AdtCarrier {
    reflect::reflect_struct(&Ty::adt("demo::Transport", vec![("value".into(), field)]))
        .expect("wrapper reflects")
}

fn generic_parameter(name: &str) -> Ty {
    Ty::Unsupported {
        kind: reflect::PARAM_KIND.into(),
        detail: format!("generic parameter {name} needs monomorphization"),
    }
}

#[test]
fn registered_carrier_round_trips_fresh_and_cached_closed_registration() {
    let carrier = wrapper(Ty::Bool);
    let name = Name::from_string(&carrier.name);
    let mut env = Environment::with_prelude();
    for _ in 0..2 {
        let registry = register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        let registered = registry.registered_carrier(&env, &name, &[]).expect("exact carrier");
        assert_eq!(registered.ty(), constant(&carrier.name));
        assert_eq!(registered.name(), &name);
        assert!(registered.arguments().is_empty());
        registered.validate_in(&env).expect("same environment still matches");
        TypeChecker::new(&env)
            .check_type(&registered.ty(), &Expr::type_())
            .expect("transported type is the actual registered Type");
    }
}

#[test]
fn registered_carrier_rejects_missing_stale_and_display_alias_registration() {
    let carrier = wrapper(Ty::Bool);
    let name = Name::from_string(&carrier.name);
    let mut env = Environment::with_prelude();
    let registry = register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let mut other = Environment::with_prelude();
    assert!(registry.registered_carrier(&other, &name, &[]).is_err());
    let changed = wrapper(Ty::Int { width: 32, signed: false });
    let changed_registry = register_adt_carriers(&mut other, &[changed]);
    assert!(!changed_registry.is_empty(), "wrong-shape environment is genuinely populated");
    assert!(registry.registered_carrier(&other, &name, &[]).is_err());

    let display_alias = Name::anon().str(&carrier.name);
    assert_eq!(display_alias.to_string(), name.to_string());
    assert_ne!(display_alias, name);
    assert!(registry.registered_carrier(&env, &display_alias, &[]).is_err());
    assert!(AdtRegistry::default().registered_carrier(&env, &name, &[]).is_err());
}

#[test]
fn registered_carrier_keeps_exact_generic_arguments_and_rejects_bad_arguments() {
    let carrier = reflect::reflect_struct(&Ty::adt(
        "demo::TransportPair",
        vec![
            ("first".into(), generic_parameter("T/#0")),
            ("second".into(), generic_parameter("U/#1")),
        ],
    ))
    .expect("generic pair reflects");
    assert_eq!(carrier.type_params.len(), 2);
    let name = Name::from_string(&carrier.name);
    let mut env = Environment::with_prelude();
    let registry = register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    let arguments = [constant("Bool"), constant("Nat")];
    let registered = registry.registered_carrier(&env, &name, &arguments).expect("closed pair");
    assert_eq!(registered.arguments(), &arguments);
    assert_eq!(registered.ty(), Expr::apps(constant(&carrier.name), arguments.clone()));
    let reversed = registry
        .registered_carrier(&env, &name, &[constant("Nat"), constant("Bool")])
        .expect("other instantiation is independently valid");
    assert_ne!(registered, reversed, "argument order must not collapse distinct instances");
    assert_ne!(registered.ty(), reversed.ty());
    for bad in [
        vec![],
        vec![constant("Bool")],
        vec![constant("Bool"), constant("Nat"), constant("Bool")],
        vec![constant("Bool.true"), constant("Nat")],
        vec![Expr::bvar(0), constant("Nat")],
        vec![Expr::type_(), constant("Nat")],
    ] {
        assert!(registry.registered_carrier(&env, &name, &bad).is_err(), "accepted {bad:?}");
    }
}

#[test]
fn registered_carrier_declines_reordered_enum_constructors_on_cached_readmission() {
    let carrier = reflect::reflect_enum(&Ty::adt_enum(
        "demo::TransportChoice",
        vec![
            VariantDef {
                name: "Left".into(),
                discriminant: 0,
                fields: vec![("value".into(), Ty::Bool)],
            },
            VariantDef {
                name: "Right".into(),
                discriminant: 1,
                fields: vec![("value".into(), Ty::Bool)],
            },
        ],
    ))
    .expect("enum reflects");
    let name = Name::from_string(&carrier.name);
    let mut env = Environment::with_prelude();
    let registry = register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
    registry.registered_carrier(&env, &name, &[]).expect("original ordered enum");

    // Names and per-name constructor types are unchanged. Only declaration
    // order differs, which the earlier set-shaped cache check could not see.
    let mut reordered = carrier.clone();
    reordered.constructors.swap(0, 1);
    assert!(!adt_matches_declared_shape(&env, &reordered));
    let rejected = register_adt_carriers(&mut env, std::slice::from_ref(&reordered));
    assert!(rejected.get(&carrier.name).is_none());
    assert!(rejected.registered_carrier(&env, &name, &[]).is_err());

    // A registry carrying the old order must also fail against a fresh kernel
    // environment that genuinely declared the opposite order.
    let mut other = Environment::with_prelude();
    let other_registry = register_adt_carriers(&mut other, &[reordered]);
    assert!(!other_registry.is_empty());
    assert!(registry.registered_carrier(&other, &name, &[]).is_err());
    let unchanged = register_adt_carriers(&mut env, &[carrier]);
    unchanged.registered_carrier(&env, &name, &[]).expect("original shape still readmits");
}
