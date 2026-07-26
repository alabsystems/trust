use super::{
    TargetTuple, evidence_inert_target_llvm_args_error, trust_target_spec_binding_error,
};

fn json_target(contents: &str) -> TargetTuple {
    TargetTuple::TargetJson {
        path_for_rustdoc: "/tmp/target.json".into(),
        tuple: "target".to_string(),
        contents: contents.to_string(),
    }
}

#[test]
fn authenticated_target_binding_hashes_the_captured_parse_bytes() {
    let target = json_target("{}");
    let digest = "44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a";
    assert_eq!(trust_target_spec_binding_error(&target, Some(digest), true), None);
    assert!(trust_target_spec_binding_error(&target, None, true).is_some());
    assert!(
        trust_target_spec_binding_error(
            &target,
            Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"),
            true,
        )
        .is_some()
    );
    assert_eq!(trust_target_spec_binding_error(&target, None, false), None);
    assert!(
        trust_target_spec_binding_error(
            &TargetTuple::from_tuple("x86_64-unknown-linux-gnu"),
            Some(digest),
            true,
        )
        .is_some()
    );
    assert_eq!(
        trust_target_spec_binding_error(
            &TargetTuple::from_tuple("x86_64-unknown-linux-gnu"),
            None,
            true,
        ),
        None,
        "an exact built-in tuple remains admissible"
    );
    let named = trust_target_spec_binding_error(
        &TargetTuple::from_tuple("workspace-shadow-target"),
        None,
        true,
    )
    .expect("authenticated named custom target must fail before target search");
    assert!(named.contains("named non-built-in target"), "{named}");
    assert!(named.contains("RUST_TARGET_PATH"), "{named}");
    assert_eq!(
        trust_target_spec_binding_error(
            &TargetTuple::from_tuple("workspace-shadow-target"),
            None,
            false,
        ),
        None,
        "ordinary rustc keeps named custom-target resolution compatibility"
    );
}

#[test]
fn evidence_inert_target_llvm_args_accept_only_exact_builtins() {
    let builtin = TargetTuple::from_tuple("x86_64-unknown-linux-gnu");
    assert_eq!(evidence_inert_target_llvm_args_error(&builtin, true), None);

    for target in [
        TargetTuple::from_tuple("workspace-shadow-target"),
        json_target("{}"),
        TargetTuple::TargetJson {
            path_for_rustdoc: "/tmp/x86_64-unknown-linux-gnu.json".into(),
            tuple: "x86_64-unknown-linux-gnu".to_string(),
            contents: "{}".to_string(),
        },
    ] {
        assert!(
            evidence_inert_target_llvm_args_error(&target, true).is_some(),
            "custom target `{target}` escaped LLVM-argument rejection",
        );
        assert_eq!(evidence_inert_target_llvm_args_error(&target, false), None);
    }
}
