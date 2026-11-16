//! Required named binary execution must not narrow the normal test selection.
#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;

use crate::prelude::*;
use cargo_test_support::{Execs, Project, ProjectBuilder, project, rustc_host};

const REQUIRED: &str = "required-bin";

fn recording_test(tag: &str) -> String {
    format!(
        r#"
        #[test]
        fn records_execution() {{
            use std::io::Write;
            let path = std::env::var_os("REQUIRE_BIN_COUNTER").unwrap();
            let mut file = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
            file.write_all(b"{tag}\n").unwrap();
        }}
        "#
    )
}

fn bin_project(options: &str, source: &str) -> ProjectBuilder {
    project()
        .file(
            "Cargo.toml",
            &format!(
                r#"
                [package]
                name = "foo"
                version = "0.1.0"
                edition = "2021"
                autobins = false

                [lib]
                doctest = false

                [[bin]]
                name = "required-bin"
                path = "src/cli.rs"
                {options}
                "#
            ),
        )
        .file("src/lib.rs", &recording_test("lib"))
        .file("src/cli.rs", source)
}

fn command(p: &Project, args: &str) -> Execs {
    let mut command = p.cargo(args);
    command.env("REQUIRE_BIN_COUNTER", p.root().join("calls"));
    command
}

fn refused(mut command: Execs, diagnostic: &str) {
    let output = command
        .without_status()
        .with_stderr_contains(&format!("[..]{diagnostic}[..]"))
        .run();
    assert!(
        matches!(output.code, Some(code) if code != 0),
        "required test refusal returned success: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn no_execution(p: &Project) {
    assert!(
        !p.root().join("calls").exists(),
        "a test ran before refusal"
    );
}

#[cargo_test]
fn missing_binary_is_not_satisfied_by_a_passing_library() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2021"
            autobins = false
            [lib]
            doctest = false
            "#,
        )
        .file("src/lib.rs", &recording_test("lib"))
        .build();
    for args in [
        "test --require-test-bin required-bin",
        "test --all-targets --require-test-bin required-bin",
    ] {
        refused(
            command(&p, args),
            "required test binary `required-bin` must occur exactly once in the resolved test execution inventory (found 0)",
        );
        no_execution(&p);
    }
}

#[cargo_test]
fn test_false_is_not_a_resolved_binary_test() {
    let p = bin_project(
        "test = false",
        &format!("fn main() {{}} {}", recording_test("bin")),
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin"),
        "required test binary `required-bin` must occur exactly once in the resolved test execution inventory (found 0)",
    );
    no_execution(&p);
}

#[cargo_test]
fn unavailable_required_features_are_not_silent_success() {
    let p = bin_project(
        "required-features = [\"cli\"]\n[features]\ncli = []",
        &format!("fn main() {{}} {}", recording_test("bin")),
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin"),
        "required test binary `required-bin` must occur exactly once in the resolved test execution inventory (found 0)",
    );
    no_execution(&p);
}

#[cargo_test]
fn custom_harness_cannot_forge_a_passing_summary() {
    let p = bin_project(
        "harness = false",
        r#"
        fn main() {
            std::fs::write(std::env::var_os("REQUIRE_BIN_COUNTER").unwrap(), b"custom\n").unwrap();
            println!("test result: ok. 1 passed; 0 failed; 0 ignored;");
        }
        "#,
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin"),
        "required test binary `required-bin` must use the Rust test harness",
    );
    no_execution(&p);
}

#[cargo_test]
fn matching_integration_name_is_not_a_binary() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2021"
            autobins = false
            [lib]
            doctest = false
            [[test]]
            name = "required-bin"
            path = "tests/named.rs"
            "#,
        )
        .file("src/lib.rs", &recording_test("lib"))
        .file("tests/named.rs", &recording_test("integration"))
        .build();
    refused(
        command(&p, "test --require-test-bin required-bin"),
        "required test binary `required-bin` must occur exactly once in the resolved test execution inventory (found 0)",
    );
    no_execution(&p);
}

#[cargo_test]
fn duplicate_workspace_binary_names_are_ambiguous() {
    let mut builder = project().file(
        "Cargo.toml",
        "[workspace]\nmembers = [\"a\", \"b\"]\nresolver = \"2\"\n",
    );
    for name in ["a", "b"] {
        builder = builder
            .file(
                format!("{name}/Cargo.toml"),
                &format!(
                    r#"
                    [package]
                    name = "{name}"
                    version = "0.1.0"
                    edition = "2021"
                    autobins = false
                    [[bin]]
                    name = "required-bin"
                    path = "src/main.rs"
                    "#
                ),
            )
            .file(
                format!("{name}/src/main.rs"),
                &format!("fn main() {{}} {}", recording_test(name)),
            );
    }
    let p = builder.build();
    refused(
        command(&p, "test --workspace --require-test-bin required-bin"),
        "required test binary `required-bin` must occur exactly once in the resolved test execution inventory (found 2)",
    );
    no_execution(&p);
}

#[cargo_test]
fn zero_tests_are_not_satisfied_by_another_passing_target() {
    let p = bin_project("", "fn main() {}").build();
    refused(
        command(&p, "test --require-test-bin required-bin --no-fail-fast"),
        "required test binary `required-bin` reported no passing tests",
    );
}

// Trust: child harness chatter must not replace the required harness's completion.
#[cargo_test]
fn duplicate_stdout_summaries_are_not_harness_completion() {
    let p = bin_project(
        "",
        r#"
fn main() {}
#[test]
fn extra_footer() {
    use std::io::Write;
    let footer = concat!(
        "\ntest result: ok. 1 passed; 0 failed; 0 ignored; ",
        "0 measured; 0 filtered out; finished in 0.00s\n",
    );
    std::io::stdout().write_all(footer.as_bytes()).unwrap();
}
"#,
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin -- --nocapture"),
        "required test binary `required-bin` reported no passing tests",
    );
}

#[cargo_test]
fn ignored_only_is_not_positive_execution() {
    let p = bin_project(
        "",
        "fn main() {}\n#[test] #[ignore] fn not_executed() { panic!(\"ignored\"); }",
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin --no-fail-fast"),
        "required test binary `required-bin` reported no passing tests",
    );
}

#[cargo_test]
fn exiting_before_the_harness_summary_is_not_positive_execution() {
    let p = bin_project(
        "",
        "fn main() {}\n#[test] fn exits_early() { std::process::exit(0); }",
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin --no-fail-fast"),
        "required test binary `required-bin` reported no passing tests",
    );
}

#[cargo_test]
fn failing_required_test_is_not_replaced_by_another_target_success() {
    let p = bin_project(
        "",
        "fn main() {}\n#[test] fn required_failure() { panic!(\"required bin red\"); }",
    )
    .build();
    let output = command(&p, "test --require-test-bin required-bin --no-fail-fast")
        .without_status()
        .with_stdout_contains("test required_failure ... FAILED")
        .with_stderr_contains("[..]test failed[..]")
        .run();
    assert!(matches!(output.code, Some(code) if code != 0));
}

#[cargo_test]
fn full_default_selection_executes_each_harness_once() {
    let p = bin_project("", &format!("fn main() {{}} {}", recording_test("bin")))
        .file("tests/integration.rs", &recording_test("integration"))
        .build();
    command(&p, "test --require-test-bin required-bin --no-fail-fast").run();
    let calls = fs::read_to_string(p.root().join("calls")).unwrap();
    let mut calls = calls.lines().collect::<Vec<_>>();
    calls.sort_unstable();
    assert_eq!(calls, ["bin", "integration", "lib"]);
}

#[cargo_test]
fn custom_target_runner_is_refused() {
    let p = bin_project("", &format!("fn main() {{}} {}", recording_test("bin"))).build();
    let host = rustc_host();
    let runner_env = format!(
        "CARGO_TARGET_{}_RUNNER",
        host.replace('-', "_").to_uppercase()
    );
    let mut cmd = command(
        &p,
        &format!("test --target {host} --require-test-bin {REQUIRED}"),
    );
    cmd.env(&runner_env, "required-bin-runner-must-not-execute");
    refused(
        cmd,
        "required test binary `required-bin` does not support a custom target runner",
    );
    no_execution(&p);
}

#[cargo_test]
fn no_run_cannot_promise_later_execution() {
    let p = bin_project("", &format!("fn main() {{}} {}", recording_test("bin"))).build();
    let output = command(&p, "test --require-test-bin required-bin --no-run")
        .without_status()
        .with_stderr_contains("[..]--require-test-bin[..]")
        .with_stderr_contains("[..]--no-run[..]")
        .run();
    assert!(matches!(output.code, Some(code) if code != 0));
    no_execution(&p);
}

#[cargo_test]
fn stderr_summary_cannot_replace_harness_completion() {
    let p = bin_project(
        "",
        r#"
        fn main() {}
        #[test]
        fn exits_after_forging_stderr() {
            use std::io::Write;
            std::io::stderr().write_all(
                b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n"
            ).unwrap();
            std::process::exit(0);
        }
        "#,
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin --no-fail-fast"),
        "required test binary `required-bin` reported no passing tests",
    );
}

// Register the forged stderr line at process exit, after libtest emits its
// genuine zero-test stdout summary. These are the two supported object formats
// for this constructor-only fixture; no custom test harness or runner is used.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[cargo_test]
fn real_zero_test_summary_is_not_overridden_by_stderr() {
    let p = bin_project(
        "",
        r#"
        use std::io::Write;
        unsafe extern "C" {
            fn atexit(callback: extern "C" fn()) -> std::ffi::c_int;
        }
        extern "C" fn forge_stderr_at_exit() {
            let _ = std::io::stderr().write_all(
                b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s\n"
            );
        }
        extern "C" fn register() {
            assert_eq!(unsafe { atexit(forge_stderr_at_exit) }, 0);
        }
        #[used]
        #[cfg_attr(target_os = "linux", unsafe(link_section = ".init_array"))]
        #[cfg_attr(target_os = "macos", unsafe(link_section = "__DATA,__mod_init_func"))]
        static INIT: extern "C" fn() = register;
        fn main() {}
        "#,
    )
    .build();
    let output = command(&p, "test --require-test-bin required-bin --no-fail-fast")
        .without_status()
        .with_stdout_contains("test result: ok. 0 passed; 0 failed;[..]")
        .with_stderr_contains("test result: ok. 1 passed; 0 failed;[..]")
        .with_stderr_contains(
            "[..]required test binary `required-bin` reported no passing tests[..]",
        )
        .run();
    assert!(matches!(output.code, Some(code) if code != 0));
}

#[cargo_test]
fn truncated_stdout_summary_is_not_harness_completion() {
    let p = bin_project(
        "",
        r#"
        fn main() {}
        #[test]
        fn exits_after_truncated_stdout() {
            use std::io::Write;
            std::io::stdout().write_all(b"\ntest result: ok. 1 passed; 0 failed;\n").unwrap();
            std::process::exit(0);
        }
        "#,
    )
    .build();
    refused(
        command(&p, "test --require-test-bin required-bin --no-fail-fast"),
        "required test binary `required-bin` reported no passing tests",
    );
}
