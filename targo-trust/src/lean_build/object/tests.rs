use super::*;

fn invocation(source: &str) -> (tempfile::TempDir, Vec<String>, std::path::PathBuf) {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("Main.lean");
    let output = directory.path().join("Main.o");
    std::fs::write(&input, source).unwrap();
    let args = vec![
        input.display().to_string(),
        "--emit=object".into(),
        "--out".into(),
        output.display().to_string(),
    ];
    (directory, args, output)
}

#[test]
fn unsupported_sibling_and_runtime_and_false_proof_refuse_whole_cli_object() {
    for source in [
        "def add64 (a b : UInt64) : UInt64 := a + b\ndef heapValue : Nat := 999999999999999999999999999999999\n",
        "def recursive (n : Nat) : Nat := match n with | 0 => 0 | n + 1 => recursive n\n",
        "theorem bad : False := True.intro\n",
    ] {
        let (_directory, args, output) = invocation(source);
        assert_ne!(run(&args), ExitCode::SUCCESS);
        assert!(!output.exists());
    }
}

#[test]
fn existing_output_and_unplaceable_argument_abi_are_refused() {
    let (_directory, args, output) = invocation("def add64 (a b : UInt64) : UInt64 := a + b\n");
    std::fs::write(&output, b"previous object").unwrap();
    assert_ne!(run(&args), ExitCode::SUCCESS);
    assert_eq!(std::fs::read(&output).unwrap(), b"previous object");
    let (_directory, args, output) =
        invocation("def ninth (a b c d e f g h i : UInt64) : UInt64 := i\n");
    let request = parse(&args).unwrap();
    let error = super::super::build_artifact(&request, true).unwrap_err();
    assert!(error.render(false).contains("more than 8 integer argument registers"));
    assert!(!output.exists());
}

#[test]
fn command_parser_does_not_offer_unknown_or_runtime_escape_hatches() {
    let (_directory, mut args, _output) = invocation("def answer : UInt64 := 42\n");
    assert!(requested(&args));
    assert!(parse(&args).is_ok());
    for flag in ["--allow-unknown", "--entry", "--emit=diagnostic-runtime-trust-ir"] {
        args.push(flag.into());
        assert!(parse(&args).is_err());
        args.pop();
    }
}
