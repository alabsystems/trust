// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Live registration plus passive-codec regression tests; no decoding authority.

use clean_auto::bridge::ay_contract::deserialize_term;

use super::*;

fn registered(env: &mut Environment, schema: &AdtSchema) -> RegisteredAdt {
    install(env, schema);
    RegisteredAdt::validate(env, schema, &[]).unwrap()
}

#[test]
fn canonical_binding_is_stable_and_retains_the_exact_type() {
    let mut env = base();
    let schema = enumeration(Name::from_string("BindingEnum"), Expr::const_str("Bool"));
    let handle = registered(&mut env, &schema);
    let bytes = handle.canonical_binding(&env).unwrap();
    assert_eq!(bytes, handle.canonical_binding(&env.clone()).unwrap());
    let payload = bytes.strip_prefix(b"trust-spec-elab.registered-adt.binding.v1\0").unwrap();
    let length = usize::try_from(u64::from_le_bytes(payload[..8].try_into().unwrap())).unwrap();
    assert_eq!(deserialize_term(&payload[8..8 + length]).unwrap(), handle.ty());
    env.add_decl(Declaration::Definition {
        name: Name::from_string("binding_unrelated"),
        level_params: vec![],
        type_: Expr::const_str("Bool"),
        value: Expr::const_str("Bool.true"),
        is_reducible: true,
    })
    .unwrap();
    assert_eq!(bytes, handle.canonical_binding(&env).unwrap());
    let rebuilt = RegisteredAdt::validate(&env, &schema, &[]).unwrap();
    assert_eq!(bytes, rebuilt.canonical_binding(&env).unwrap());
    assert!(canonical_declaration_binding(&env, &Name::from_string("MissingBinding")).is_err());
}

#[test]
fn changed_order_or_field_type_changes_binding_and_refuses_stale_handle() {
    let schema = enumeration(Name::from_string("BindingEnum"), Expr::const_str("Bool"));
    let mut env = base();
    let old = registered(&mut env, &schema);
    let before = old.canonical_binding(&env).unwrap();
    let before_record = canonical_declaration_binding(&env, &schema.name).unwrap();
    for changed in [
        AdtSchema {
            constructors: schema.constructors.iter().rev().cloned().collect(),
            ..schema.clone()
        },
        enumeration(schema.name.clone(), Expr::const_str("Nat")),
    ] {
        let mut other = base();
        let new = registered(&mut other, &changed);
        assert_eq!(new.ty(), old.ty(), "type syntax alone misses changed registrations");
        assert_ne!(before, new.canonical_binding(&other).unwrap());
        assert!(old.canonical_binding(&other).is_err());
        if changed.constructors[0].name != schema.constructors[0].name {
            assert_ne!(before_record, canonical_declaration_binding(&other, &schema.name).unwrap());
        }
    }
}

#[test]
fn binding_preserves_arguments_alias_dependencies_and_provenance() {
    let (env, schema) = alias_environment("Bool", false);
    let old = RegisteredAdt::validate(&env, &schema, &[]).unwrap();
    let (changed, _) = alias_environment("Nat", false);
    let new = RegisteredAdt::validate(&changed, &schema, &[]).unwrap();
    assert_eq!(old.ty(), new.ty());
    assert_ne!(old.canonical_binding(&env).unwrap(), new.canonical_binding(&changed).unwrap());
    assert!(old.canonical_binding(&changed).is_err());
    let (structural, _) = alias_environment("Bool", true);
    assert!(old.canonical_binding(&structural).is_err());
    let alias = Name::from_string("PayloadAlias");
    // Passive single-record readback is deliberately not a provenance audit.
    assert_ne!(
        canonical_declaration_binding(&env, &alias).unwrap(),
        canonical_declaration_binding(&structural, &alias).unwrap()
    );
    let mut partial = env.clone();
    partial.mark_partial(alias.clone());
    assert!(old.canonical_binding(&partial).is_err());
    assert_ne!(
        canonical_declaration_binding(&env, &alias).unwrap(),
        canonical_declaration_binding(&partial, &alias).unwrap()
    );

    let mut env = base();
    let schema = pair();
    install(&mut env, &schema);
    let forward =
        RegisteredAdt::validate(&env, &schema, &[Expr::const_str("Bool"), Expr::const_str("Nat")])
            .unwrap();
    let reverse =
        RegisteredAdt::validate(&env, &schema, &[Expr::const_str("Nat"), Expr::const_str("Bool")])
            .unwrap();
    assert_ne!(forward.canonical_binding(&env).unwrap(), reverse.canonical_binding(&env).unwrap());
}

#[test]
fn display_collisions_do_not_alias_declaration_or_carrier_bindings() {
    let mut env = base();
    let a = enumeration(Name::from_string("Binding.same"), Expr::const_str("Bool"));
    let b = enumeration(Name::anon().str("Binding.same"), Expr::const_str("Bool"));
    assert_eq!(a.name.to_string(), b.name.to_string());
    let first = registered(&mut env, &a);
    let second = registered(&mut env, &b);
    assert_ne!(
        canonical_declaration_binding(&env, &a.name).unwrap(),
        canonical_declaration_binding(&env, &b.name).unwrap()
    );
    assert_ne!(first.canonical_binding(&env).unwrap(), second.canonical_binding(&env).unwrap());
}

#[test]
fn passive_snapshot_encoding_includes_side_tables_and_lookup_key() {
    // Deliberately mutate detached snapshots, not Environment registrations:
    // this tests wire coverage, not acceptance of malformed kernel metadata.
    let mut env = base();
    let schema = enumeration(Name::from_string("BindingEnum"), Expr::const_str("Bool"));
    install(&mut env, &schema);
    let key = Name::append(&schema.name, "rec");
    let original = DeclarationSnapshot::read(&env, &key).unwrap();
    let baseline = binding::declaration(&key, &original).unwrap();
    let mut changed = original.clone();
    changed.recursor.as_mut().unwrap().9[0].3 = Expr::bvar(0);
    assert_ne!(baseline, binding::declaration(&key, &changed).unwrap());
    changed = original.clone();
    changed.recursor.as_mut().unwrap().9[0].2.push(true);
    assert_ne!(baseline, binding::declaration(&key, &changed).unwrap());
    changed = original.clone();
    changed.fields = Some(vec![Name::from_string("field")]);
    assert_ne!(baseline, binding::declaration(&key, &changed).unwrap());
    changed = original.clone();
    changed.verification = None;
    assert_ne!(baseline, binding::declaration(&key, &changed).unwrap());
    assert_ne!(baseline, binding::declaration(&Name::from_string("OtherKey"), &original).unwrap());
}

#[test]
fn environment_binding_reaches_unused_constructors_and_keeps_root_order() {
    let (env, schema) = alias_environment("Bool", false);
    let (changed, _) = alias_environment("Nat", false);
    // The former itself has no payload reference. The closure must walk its
    // constructor table to discover PayloadAlias, then bind its changed body.
    assert_eq!(
        canonical_declaration_binding(&env, &schema.name).unwrap(),
        canonical_declaration_binding(&changed, &schema.name).unwrap()
    );
    let roots = [schema.name.clone()];
    assert_ne!(
        canonical_environment_binding(&env, &roots).unwrap(),
        canonical_environment_binding(&changed, &roots).unwrap()
    );
    let dependencies = audit_dependencies(&env, roots.iter().cloned().collect()).unwrap();
    assert!(dependencies.contains_key(&Name::append(&schema.name, "rec")));
    assert!(dependencies.contains_key(&Name::from_string("PayloadAlias")));
    let a = [schema.name.clone(), Name::from_string("PayloadAlias")];
    let b = [a[1].clone(), a[0].clone()];
    assert_ne!(
        canonical_environment_binding(&env, &a).unwrap(),
        canonical_environment_binding(&env, &b).unwrap()
    );
    assert!(canonical_environment_binding(&env, &vec![schema.name.clone(); 4097]).is_err());
    assert!(canonical_environment_binding(&env, &[Name::from_string("MissingRoot")]).is_err());
    let (structural, _) = alias_environment("Bool", true);
    assert!(canonical_environment_binding(&structural, &roots).is_err());
}
