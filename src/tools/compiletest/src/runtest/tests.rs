use super::*;

#[test]
fn grounded_row_patterns_bind_the_aggregate_and_its_own_final_grade() {
    // Exercise the actual UI directives with the same regex engine as the
    // harness. A valid sibling certificate must never repair a bad aggregate.
    let fixture =
        include_str!("../../../../../tests/ui/trust/grounded_catchall_inherits_weakest_premise.rs");
    let mut checked = 0;
    for line in fixture.lines() {
        let Some((_, pattern)) = line.split_once("regex-error-pattern: ") else { continue };
        let regex = Regex::new(pattern).expect("valid row pattern");
        let function = pattern
            .split("\"function\":\"")
            .nth(1)
            .expect("function identity")
            .split('"')
            .next()
            .unwrap();
        let aggregate = pattern.contains("assertion: panic freedom: ");
        let ceiling = pattern.contains("compiler-composed|solver-asserted|solver-self-checked");
        let description = if aggregate {
            "assertion: panic freedom: no assertion, `unreachable!`, or panic is reachable"
        } else {
            "assertion: panic call: core::panicking::panic_default_msg"
        };
        let discharge = if ceiling { "compiler-composed" } else { "kernel-reference-checked" };
        let record = |name: &str, description: &str, discharge: &str| {
            let suffix = if aggregate {
                if name.ends_with("::guard_behind_a_call") {
                    ":assertion:panic-freedom:0"
                } else {
                    ":assert:0"
                }
            } else {
                ":assertion:0"
            };
            let id = format!("vc:{}{suffix}", name.replace("::", "__"));
            format!(
                "TRUST_ROW_DIAGNOSTIC:{{\"function\":{name},\"row\":{{\"obligation_id\":{id},\"kind\":\"assert\",\"description\":{description},\"outcome\":\"proved\",\"solver\":\"fixture\",\"time_ms\":0,\"grade\":{{\"encoding\":\"unvalidated-encoder\",\"discharge\":\"{discharge}\",\"premises\":[]}}}}}}\n",
                name = serde_json::to_string(name).unwrap(),
                id = serde_json::to_string(&id).unwrap(),
                description = serde_json::to_string(description).unwrap(),
            )
        };
        let good = record(function, description, discharge);
        assert!(regex.is_match(&good), "positive row: {pattern}");
        assert!(!regex.is_match(&record("another::body", description, discharge)));
        if aggregate {
            let wrong_id = good.replace(&function.replace("::", "__"), "another__body");
            assert!(!regex.is_match(&wrong_id), "the aggregate ID must name its own function");
        }
        assert!(!regex.is_match(&record(function, "another assertion", discharge)));
        let bad_discharge = if ceiling { "kernel-reference-checked" } else { "compiler-composed" };
        let bad = record(function, description, bad_discharge);
        let sibling = record(function, "another assertion", discharge);
        assert!(!regex.is_match(&format!("{bad}{sibling}")), "cannot borrow a sibling grade");
        assert!(!regex.is_match(&format!("{sibling}{bad}")), "cannot borrow an earlier grade");
        // A missing own grade also cannot borrow the following sibling's.
        let own_grade = format!(
            ",\"grade\":{{\"encoding\":\"unvalidated-encoder\",\"discharge\":\"{discharge}\",\"premises\":[]}}"
        );
        let missing_grade = good.replace(&own_grade, "");
        assert!(!regex.is_match(&format!("{missing_grade}{sibling}")));
        if ceiling {
            for allowed in ["compiler-composed", "solver-asserted", "solver-self-checked"] {
                assert!(
                    regex.is_match(&record(function, description, allowed)),
                    "Trusted aggregate discharge {allowed} remains below the Certified ceiling"
                );
            }
            let runtime =
                missing_grade.replace("\"outcome\":\"proved\"", "\"outcome\":\"runtime_checked\"");
            assert!(regex.is_match(&runtime), "uncredited aggregate remains permitted");
        }
        checked += 1;
    }
    assert_eq!(checked, 13, "all aggregate ceilings and independent-site/control floors");
}

#[test]
fn normalize_platform_differences() {
    assert_eq!(TestCx::normalize_platform_differences(r"$DIR\foo.rs"), "$DIR/foo.rs");
    assert_eq!(
        TestCx::normalize_platform_differences(r"$BUILD_DIR\..\parser.rs"),
        "$BUILD_DIR/../parser.rs"
    );
    assert_eq!(
        TestCx::normalize_platform_differences(r"$DIR\bar.rs: hello\nworld"),
        r"$DIR/bar.rs: hello\nworld"
    );
    assert_eq!(
        TestCx::normalize_platform_differences(r"either bar\baz.rs or bar\baz\mod.rs"),
        r"either bar/baz.rs or bar/baz/mod.rs",
    );
    assert_eq!(TestCx::normalize_platform_differences(r"`.\some\path.rs`"), r"`./some/path.rs`",);
    assert_eq!(TestCx::normalize_platform_differences(r"`some\path.rs`"), r"`some/path.rs`",);
    assert_eq!(
        TestCx::normalize_platform_differences(r"$DIR\path-with-dashes.rs"),
        r"$DIR/path-with-dashes.rs"
    );
    assert_eq!(
        TestCx::normalize_platform_differences(r"$DIR\path_with_underscores.rs"),
        r"$DIR/path_with_underscores.rs",
    );
    assert_eq!(TestCx::normalize_platform_differences(r"$DIR\foo.rs:12:11"), "$DIR/foo.rs:12:11",);
    assert_eq!(
        TestCx::normalize_platform_differences(r"$DIR\path with\spaces 'n' quotes"),
        "$DIR/path with/spaces 'n' quotes",
    );
    assert_eq!(
        TestCx::normalize_platform_differences(r"$DIR\file_with\no_extension"),
        "$DIR/file_with/no_extension",
    );

    assert_eq!(TestCx::normalize_platform_differences(r"\n"), r"\n");
    assert_eq!(TestCx::normalize_platform_differences(r"{ \n"), r"{ \n");
    assert_eq!(TestCx::normalize_platform_differences(r"`\]`"), r"`\]`");
    assert_eq!(TestCx::normalize_platform_differences(r#""\{""#), r#""\{""#);
    assert_eq!(
        TestCx::normalize_platform_differences(r#"write!(&mut v, "Hello\n")"#),
        r#"write!(&mut v, "Hello\n")"#
    );
    assert_eq!(
        TestCx::normalize_platform_differences(r#"println!("test\ntest")"#),
        r#"println!("test\ntest")"#,
    );
}
