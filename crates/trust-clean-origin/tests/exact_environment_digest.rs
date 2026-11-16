// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact dependency identity controls. The ordinary positives use full add_decl;
//! explicitly labeled malformed-import controls do not confer kernel admission.

use clean_kernel::{Declaration, Environment, Expr, Name};
use trust_clean_origin::admission::environment_digest_for;

fn definition(env: &mut Environment, name: Name, body: Expr) {
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: Expr::const_str("Bool"),
        value: body,
        is_reducible: true,
    })
    .expect("actual full kernel admission");
}

fn boolean(value: bool) -> Expr {
    Expr::const_str(if value { "Bool.true" } else { "Bool.false" })
}

fn twins(numeric: bool) -> [Name; 2] {
    if numeric {
        [Name::anon().str("Twin").num(7), Name::anon().str("Twin").str("7")]
    } else {
        [Name::from_string("Twin.leaf"), Name::anon().str("Twin.leaf")]
    }
}

fn environment(
    names: &[Name; 2],
    values: [bool; 2],
    selected: usize,
    reverse: bool,
) -> Environment {
    assert_ne!(names[0], names[1]);
    assert_eq!(names[0].to_string(), names[1].to_string());
    let mut env = Environment::new();
    env.init_bool().unwrap();
    for index in if reverse { [1, 0] } else { [0, 1] } {
        definition(&mut env, names[index].clone(), boolean(values[index]));
    }
    definition(
        &mut env,
        Name::from_string("subject"),
        Expr::const_(names[selected].clone(), vec![]),
    );
    env
}

#[test]
fn quoted_dependency_body_is_bound() {
    let names = twins(false);
    let a = environment(&names, [true, true], 1, false);
    let b = environment(&names, [true, false], 1, false);
    assert_ne!(
        environment_digest_for(&a, "subject").unwrap(),
        environment_digest_for(&b, "subject").unwrap()
    );
}

#[test]
fn typed_subject_api_distinguishes_quoted_and_numeric_roots() {
    use trust_clean_origin::admission::environment_digest_for_name;
    for numeric in [false, true] {
        let names = twins(numeric);
        let env = environment(&names, [true, true], 1, false);
        assert_ne!(
            environment_digest_for_name(&env, &names[0]).unwrap(),
            environment_digest_for_name(&env, &names[1]).unwrap()
        );
        assert_eq!(
            environment_digest_for_name(&env, &Name::from_string("subject")).unwrap(),
            environment_digest_for(&env, "subject").unwrap()
        );
    }
}

#[test]
fn shared_and_independently_allocated_terms_have_equal_digests() {
    use clean_kernel::{BinderInfo, Level};
    let make = |shared: bool| {
        let mut env = Environment::new();
        env.init_bool().unwrap();
        let leaf = boolean(true);
        let other = if shared { leaf.clone() } else { boolean(true) };
        let body = Expr::apps(
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]),
            [
                Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), Expr::const_str("Bool")),
                leaf,
                other,
                boolean(true),
            ],
        );
        definition(&mut env, Name::from_string("subject"), body);
        env
    };
    assert_eq!(
        environment_digest_for(&make(true), "subject").unwrap(),
        environment_digest_for(&make(false), "subject").unwrap()
    );
}

#[test]
fn old_printed_digest_mode_is_refused_before_payload_processing() {
    use trust_clean_origin::admission::{DecodeRefusal, VerdictDigest, local_kernel_version};
    let mut wire = b"TVDG\x02".to_vec();
    for text in ["subject", local_kernel_version()] {
        wire.extend_from_slice(&(text.len() as u32).to_le_bytes());
        wire.extend_from_slice(text.as_bytes());
    }
    wire.push(1);
    assert!(matches!(
        VerdictDigest::decode(&wire),
        Err(DecodeRefusal::Malformed { field: "environment digest mode", .. })
    ));
}

#[test]
fn serialization_limit_never_returns_a_digest_and_does_not_poison_next_call() {
    use std::sync::Arc;

    use trust_clean_origin::admission::EnvironmentDigestRefusal;
    let mut env = Environment::new();
    env.init_bool().unwrap();
    let metadata = clean_kernel::MDataValue::String(Arc::from("x".repeat(16 * 1024 * 1024)));
    let body = Expr::mdata(vec![(Name::from_string("large"), metadata)], boolean(true));
    definition(&mut env, Name::from_string("oversized"), body);
    definition(&mut env, Name::from_string("small"), boolean(true));
    assert!(matches!(
        environment_digest_for(&env, "oversized"),
        Err(EnvironmentDigestRefusal::Encoding { .. })
    ));
    assert!(environment_digest_for(&env, "small").is_ok());
}

#[test]
fn oversized_environment_refuses_import_before_any_digest_comparison() {
    use std::sync::Arc;

    use trust_clean_origin::admission::{
        ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE, EnvironmentDigestRefusal, ExportDigestRefusal,
        ReadmissionRefusal, VerdictDigest, bind_readmission, local_kernel_version, preflight_wire,
    };
    let mut env = Environment::new();
    env.init_bool().unwrap();
    definition(
        &mut env,
        Name::from_string("oversized"),
        Expr::mdata(
            vec![(
                Name::from_string("large"),
                clean_kernel::MDataValue::String(Arc::from("x".repeat(16 * 1024 * 1024))),
            )],
            boolean(true),
        ),
    );

    // Untrusted but well-formed wire bytes. The fake hash and carrier never
    // purchase a preflight: the local environment must be bound first.
    let text = |bytes: &mut Vec<u8>, value: &str| {
        bytes.extend_from_slice(&(value.len() as u32).to_le_bytes());
        bytes.extend_from_slice(value.as_bytes());
    };
    let mut bytes = b"TVDG\x02".to_vec();
    text(&mut bytes, "oversized");
    text(&mut bytes, local_kernel_version());
    bytes.push(ENVIRONMENT_DIGEST_MODE_DEPENDENCY_CLOSURE);
    text(&mut bytes, &"0".repeat(64));
    bytes.extend_from_slice(&0u32.to_le_bytes()); // audited-empty claim
    bytes.extend_from_slice(&0u32.to_le_bytes()); // no arguments
    text(&mut bytes, "Bool");
    text(&mut bytes, "bool");
    bytes.push(1); // fixed-width carrier
    bytes.extend_from_slice(&1u32.to_le_bytes());
    bytes.push(1); // claimed definitional equality, not authority
    text(&mut bytes, "bool");
    let digest = VerdictDigest::decode(&bytes).unwrap();
    let wire = preflight_wire(&digest, local_kernel_version()).unwrap();
    let refusal = bind_readmission(&wire, &env).unwrap_err();
    assert_eq!(refusal.decl(), "oversized");
    assert!(refusal.note().contains("no import is admitted"));
    let ReadmissionRefusal::LocalEnvironmentRefused {
        refusal: EnvironmentDigestRefusal::Encoding { name, reason },
        ..
    } = refusal
    else {
        panic!("oversized closure must refuse before comparing the imported hash")
    };
    let export =
        ExportDigestRefusal::Environment(EnvironmentDigestRefusal::Encoding { name, reason });
    assert_eq!(export.decl(), "oversized");
    assert!(!export.is_compiler_defect());
    assert!(export.note().contains("byte limit exceeded"));
}

/// Deliberately changes a serialized side table. Both reconstructed contexts
/// have the same unknown validation provenance. Hashing one does NOT admit it.
fn mutated_rule_context(dependency_value: bool) -> Environment {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    definition(&mut env, Name::from_string("ruleOnly"), boolean(dependency_value));
    let mut snapshot: clean_kernel::env::JsonEnvironment =
        serde_json::from_str(&env.to_json().unwrap()).unwrap();
    let recursor = snapshot
        .recursors
        .iter_mut()
        .find(|row| row.name == Name::from_string("Bool.rec"))
        .unwrap();
    recursor.rules[0].rhs = Expr::const_str("ruleOnly");
    Environment::from_json(&serde_json::to_string(&snapshot).unwrap()).unwrap()
}

#[test]
fn recursor_rule_only_dependency_is_in_the_closure() {
    let a = mutated_rule_context(true);
    let b = mutated_rule_context(false);
    assert_eq!(
        a.get_const(&Name::from_string("Bool.rec")).unwrap().type_,
        b.get_const(&Name::from_string("Bool.rec")).unwrap().type_
    );
    assert_eq!(
        a.get_recursor(&Name::from_string("Bool.rec")).unwrap().rules[0].rhs,
        b.get_recursor(&Name::from_string("Bool.rec")).unwrap().rules[0].rhs
    );
    assert_ne!(
        environment_digest_for(&a, "Bool.rec").unwrap(),
        environment_digest_for(&b, "Bool.rec").unwrap()
    );
}

#[test]
fn projection_owner_is_a_dependency_even_without_a_const_node() {
    let make = |value| {
        let mut env = Environment::new();
        env.init_bool().unwrap();
        definition(&mut env, Name::from_string("projectionOnly"), boolean(value));
        // A malformed imported candidate can be fingerprinted, but this test
        // never gives it FullKernelCheck, a body certificate or CALL authority.
        env.add_decl_structural(Declaration::Definition {
            name: Name::from_string("subject"),
            level_params: vec![],
            type_: Expr::const_str("Bool"),
            value: Expr::proj(Name::from_string("projectionOnly"), 0, boolean(true)),
            is_reducible: true,
        })
        .unwrap();
        env
    };
    let a = make(true);
    let b = make(false);
    assert_ne!(
        environment_digest_for(&a, "subject").unwrap(),
        environment_digest_for(&b, "subject").unwrap()
    );
}

#[test]
fn numeric_string_dependency_body_is_bound() {
    let names = twins(true);
    let a = environment(&names, [true, true], 1, false);
    let b = environment(&names, [true, false], 1, false);
    assert_ne!(
        environment_digest_for(&a, "subject").unwrap(),
        environment_digest_for(&b, "subject").unwrap()
    );
}

#[test]
fn same_display_reference_retarget_changes_digest() {
    for numeric in [false, true] {
        let names = twins(numeric);
        let a = environment(&names, [true, false], 0, false);
        let b = environment(&names, [true, false], 1, false);
        assert_eq!(
            a.get_const(&Name::from_string("subject")).unwrap().value.as_ref().unwrap().to_string(),
            b.get_const(&Name::from_string("subject")).unwrap().value.as_ref().unwrap().to_string()
        );
        assert_ne!(
            environment_digest_for(&a, "subject").unwrap(),
            environment_digest_for(&b, "subject").unwrap()
        );
    }
}

#[test]
fn unrelated_display_twin_is_not_a_dependency() {
    for numeric in [false, true] {
        let names = twins(numeric);
        let a = environment(&names, [true, true], 1, false);
        let b = environment(&names, [false, true], 1, false);
        assert_eq!(
            environment_digest_for(&a, "subject").unwrap(),
            environment_digest_for(&b, "subject").unwrap()
        );
    }
}

#[test]
fn exact_twin_closure_remains_insertion_order_independent() {
    for numeric in [false, true] {
        let names = twins(numeric);
        let a = environment(&names, [true, false], 1, false);
        let b = environment(&names, [true, false], 1, true);
        assert_eq!(
            environment_digest_for(&a, "subject").unwrap(),
            environment_digest_for(&b, "subject").unwrap()
        );
    }
}

#[test]
fn erased_printing_metadata_cannot_alias_exact_stored_terms() {
    let make = |value| {
        let mut env = Environment::new();
        env.init_bool().unwrap();
        let body = Expr::mdata(
            vec![(Name::from_string("source"), clean_kernel::expr::MDataValue::Nat(value))],
            boolean(true),
        );
        definition(&mut env, Name::from_string("subject"), body);
        env
    };
    let a = make(1);
    let b = make(2);
    assert_eq!(
        a.get_const(&Name::from_string("subject")).unwrap().value.as_ref().unwrap().to_string(),
        b.get_const(&Name::from_string("subject")).unwrap().value.as_ref().unwrap().to_string()
    );
    assert_ne!(
        environment_digest_for(&a, "subject").unwrap(),
        environment_digest_for(&b, "subject").unwrap()
    );
}
