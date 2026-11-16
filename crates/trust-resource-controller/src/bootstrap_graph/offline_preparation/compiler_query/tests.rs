use super::*;

fn query(original: &Request) -> CompilerQuery {
    CompilerQuery {
        sequence: 1,
        command: CommandSpec {
            program: original.configured_compiler.clone(),
            arg0: None,
            args: [
                "-",
                "--crate-name",
                "___",
                "--print=file-names",
                "-Ztrust-verify=off",
                "--crate-type",
                "bin",
                "--crate-type",
                "rlib",
                "--crate-type",
                "dylib",
                "--crate-type",
                "cdylib",
                "--crate-type",
                "staticlib",
                "--crate-type",
                "proc-macro",
                "--print=sysroot",
                "--print=split-debuginfo",
                "--print=crate-name",
                "--print=cfg",
                "-Wwarnings",
            ]
            .map(|arg| arg.as_bytes().to_vec())
            .to_vec(),
            cwd: original.source_root.clone(),
            environment: original.environment.clone(),
        },
        timeout_ns: MAX_QUERY_NS,
    }
}

#[test]
fn ordinary_fetch_query_retains_complete_configured_command_and_original_binding() {
    let original = super::super::tests::request();
    let mut query = query(&original);
    query
        .command
        .environment
        .push((b"CONFIG_EMPTY".to_vec(), vec![]));
    query
        .command
        .environment
        .push((b"CONFIG_OS_BYTES".to_vec(), vec![255, 254]));
    // A configured compiler's environment is an observation of ordinary Cargo,
    // not a new replacement for the original parent's offline policy.
    query.command.environment[1].1 = b"configured-child-value".to_vec();
    let bytes = query.encode(&original, [3; 32]).unwrap();
    assert!(CompilerQuery::decode(&bytes, &original, [3; 32]).unwrap() == query);
    assert!(CompilerQuery::decode(&bytes, &original, [4; 32]).is_err());
    let mut foreign = original.clone();
    foreign.key.operation[0] ^= 1;
    assert!(CompilerQuery::decode(&bytes, &foreign, [3; 32]).is_err());
    assert!(crate::bootstrap_graph::query::Request::decode(&bytes).is_err());
    assert!(crate::bootstrap_graph::MaterializationPreparation::decode(&bytes).is_err());
    let materialization = crate::bootstrap_graph::MaterializationPreparation {
        key: original.key.graph.clone(),
        input_remaining_ns: 1_000_000_000,
    };
    assert!(CompilerQuery::decode(&materialization.encode().unwrap(), &original, [3; 32]).is_err());
    assert!(Request::decode(&bytes).is_err());
    for args in [
        &["-vV"][..],
        &["--print=sysroot"],
        &["-", "--crate-name", "___", "--print=cfg"],
    ] {
        query.command.args = args.iter().map(|arg| arg.as_bytes().to_vec()).collect();
        query.encode(&original, [3; 32]).unwrap();
    }
}

#[test]
fn preparation_query_refuses_producing_commands_foreign_programs_and_owner_aliases() {
    let original = super::super::tests::request();
    for addition in [
        "input.rs",
        "@args",
        "--target=custom.json",
        "-Clinker=foreign",
        "--emit=obj",
        "--print=target-spec-json",
    ] {
        let mut query = query(&original);
        query.command.args.push(addition.as_bytes().to_vec());
        assert!(query.encode(&original, [3; 32]).is_err());
    }
    let mut item = query(&original);
    item.command.program = b"/control-sdk/bin/trustc".to_vec();
    assert!(item.validate_for(&original).is_err());
    item = query(&original);
    item.command.arg0 = Some(original.configured_compiler.clone());
    assert!(item.validate_for(&original).is_err());
    item = query(&original);
    item.command.cwd = b"/another/source".to_vec();
    assert!(item.validate_for(&original).is_err());
    for name in [b"CARGO".as_slice(), b"RUSTC", b"CARGO_HOME"] {
        let mut item = query(&original);
        item.command.environment.retain(|(key, _)| key != name);
        item.command
            .environment
            .push((name.to_vec(), b"/replacement".to_vec()));
        assert!(item.validate_for(&original).is_err());
    }
    item = query(&original);
    item.command
        .environment
        .push(item.command.environment[0].clone());
    assert!(item.validate_for(&original).is_err());
    for timeout in [0, MAX_QUERY_NS + 1, u64::MAX] {
        let mut item = query(&original);
        item.timeout_ns = timeout;
        assert!(item.validate_for(&original).is_err());
    }
    item = query(&original);
    item.sequence = 0;
    assert!(item.validate_for(&original).is_err());
}

#[test]
fn preparation_query_codec_rejects_truncation_trailing_data_and_parent_frames() {
    let original = super::super::tests::request();
    let bytes = query(&original).encode(&original, [3; 32]).unwrap();
    for end in 0..bytes.len() {
        assert!(CompilerQuery::decode(&bytes[..end], &original, [3; 32]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(CompilerQuery::decode(&trailing, &original, [3; 32]).is_err());
    assert!(CompilerQuery::decode(&original.encode().unwrap(), &original, [3; 32]).is_err());
}
