//@ ignore-cross-compile
//! Execute the unchanged emitted caller/closure module. A copied capture frame must
//! separate state, while repeated calls and reference aliases retain one environment.
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::{Ty, binary::deserialize_module, interpret::{InterpretValue, Interpreter}};

/// Run the same complete-module assertions under the owning libtest harness.
#[test]
fn concrete_nested_once_captures_preserve_effects_failure_and_escape() {
    main();
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    rfs::write("native.rs", format!("{}\n{}", rfs::read_to_string("subject.rs"),
        rfs::read_to_string("native_assertions.rs")));
    cmd(rustc_path()).args(["native.rs", "--edition=2024", "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off", "-Coverflow-checks=on", "-Copt-level=0", "-o", "native"]).run();
    cmd("./native").run();
    cmd(rustc_path()).args(["subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=closure_state", "--emit=metadata", "-Coverflow-checks=on",
        "-Copt-level=0", "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=on",
        "-Ztrust-ir-flip=no", "-Ztrust-dump=ir:ir", "-o", "subject.rmeta"]).run();
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/closure_state.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let rows = coverage["bodies"].as_array().unwrap();
    let supported = [
        ("by_value_repeated", 2), ("by_reference_repeated", 2),
        ("copied_value_environments", 32), ("moved_reference_environment", 2),
        ("moved_current_environment", 2), ("mutable_reference_alias", 3),
        ("captured_reference_alias", 2),
        ("shared_reference_alias", 10), ("borrowed_array_capture", 1),
        ("destructured_value_environment", 2), ("destructured_shared_environment", 10),
    ];
    let module = deserialize_module(&rfs::read("ir/closure_state.trust-ir.bin")).unwrap();
    let interpreter = Interpreter::with_module(&module);
    for (name, expected) in supported {
        for path in [name.to_string(), format!("{name}::{{closure#0}}") ] {
            let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == path).collect();
            assert_eq!(found.len(), 1, "missing/duplicate coverage for {path}");
            assert_eq!(found[0]["lowered"], true, "{path}: {}", found[0]);
            assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{path}: {}", found[0]);
        }
        let found: Vec<_> = module.functions.iter()
            .filter(|function| function.display_path.as_deref() == Some(name)).collect();
        assert_eq!(found.len(), 1, "missing/duplicate emitted caller {name}");
        let result = interpreter.execute_func(found[0].id, []).unwrap_or_else(|error|
            panic!("{name}: unchanged complete emitted module failed: {error:?}"));
        assert_eq!(result.host_calls, 0, "{name}: no opaque host-call substitution");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, expected).unwrap()], "{name}");
    }
    for (name, when_false, when_true) in [("branch_initialized", 7, 7),
        ("match_initialized", 2, 2), ("tuple_branch_initialized", 9, 8)] {
        for path in [name.to_string(), format!("{name}::{{closure#0}}") ] {
            let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == path).collect();
            assert_eq!(found.len(), 1, "missing/duplicate coverage for {path}");
            assert_eq!(found[0]["lowered"], true, "{path}: {}", found[0]);
            assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{path}: {}", found[0]);
        }
        let found: Vec<_> = module.functions.iter()
            .filter(|function| function.display_path.as_deref() == Some(name)).collect();
        assert_eq!(found.len(), 1, "missing/duplicate delayed-init caller {name}");
        for flag in [false, true] {
            let expected = if flag { when_true } else { when_false };
            let result = interpreter.execute_func(found[0].id, [InterpretValue::bool(flag)])
                .unwrap_or_else(|error| panic!("{name}({flag}): {error:?}"));
            assert_eq!(result.host_calls, 0, "{name}({flag})");
            assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, expected).unwrap()],
                "{name}({flag})");
        }
    }
    // The source wrapper creates the reference in the interpreter's own memory.
    // Execute its real caller, FnOnce adapter and closure body without modifying IR.
    for path in ["once_guard_local", "once_guard", "once_guard::{closure#0}"] {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == path).collect();
        assert_eq!(found.len(), 1, "missing/duplicate coverage for {path}");
        assert_eq!(found[0]["lowered"], true, "{path}: {}", found[0]);
        assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{path}: {}", found[0]);
    }
    let found: Vec<_> = module.functions.iter()
        .filter(|function| function.display_path.as_deref() == Some("once_guard_local")).collect();
    assert_eq!(found.len(), 1, "missing/duplicate emitted FnOnce source wrapper");
    let result = interpreter.execute_func(found[0].id, []).unwrap_or_else(|error|
        panic!("once_guard_local: unchanged complete emitted module failed: {error:?}"));
    assert_eq!(result.host_calls, 0, "once_guard_local: no opaque host-call substitution");
    assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, 7).unwrap()]);
    for (name, expected) in [("nested_once_effects", 10), ("nested_once_failure", 51),
        ("distinct_nested_once_targets", 417), ("zero_capture_once", 41),
        ("zero_capture_once_receiver_effects", 141), ("zero_capture_direct_fn", 43),
        ("zero_capture_direct_fn_mut_request", 47)] {
        let caller = rows.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(caller["lowered"], true, "{name}: {caller}");
        assert!(caller["unsupported"].as_array().unwrap().is_empty(), "{name}: {caller}");
        assert_eq!(caller["spliced"], true, "{name}: original caller must be assembled: {caller}");
        assert!(caller["splice_refusal"].is_null(), "{name}: {caller}");
        let function = module.functions.iter()
            .find(|function| function.display_path.as_deref() == Some(name))
            .unwrap_or_else(|| panic!("{name}: original lowered caller is missing: {caller}"));
        let result = interpreter.execute_func(function.id, []).unwrap();
        assert_eq!(result.host_calls, 0, "{name}: no substituted callable");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, expected).unwrap()], "{name}");
        // Query the actual assembled module, including its real adapter body.
        // Capture layout or a source-origin label alone cannot supply code.
        let mut constructors = 0;
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            if let trust_ir::reference::Inst::MakeClosure { ty, func, .. } = &node.inst {
                constructors += 1;
                let binding = module.closure_storage_binding(*ty).unwrap_or_else(|reason|
                    panic!("{name}: original closure frame lacks checked target: {reason}"));
                assert_eq!(binding.target, *func);
                assert!(binding.layout.origin.is_some(), "{name}: concrete source origin missing");
            }
        }
        assert!(constructors > 0, "{name}: no actual closure constructors checked");
        if name == "distinct_nested_once_targets" {
            let homes = function.blocks.iter().flat_map(|block| &block.body)
                .filter_map(|node| match &node.inst {
                    trust_ir::reference::Inst::Alloca { ty: Ty::Closure(_), .. } => node.results.first().copied(),
                    _ => None,
                }).collect::<Vec<_>>();
            assert_eq!(homes.len(), 1, "one lifetime-long original environment home");
            assert!(function.blocks.iter().flat_map(|block| &block.body).any(|node|
                matches!(&node.inst, trust_ir::reference::Inst::Store {
                    ty: Ty::Closure(_), ptr, ..
                } if *ptr == homes[0])), "the actual closure image initializes its home");
        }
    }
    let escaped = rows.iter().find(|row| row["def_path"] == "nested_once_escape_guard").unwrap();
    assert_eq!(escaped["lowered"], false, "nested environment must preserve stack provenance");
    let escaped = rows.iter().find(|row| row["def_path"] == "once_home_address_escape_guard").unwrap();
    assert_eq!(escaped["lowered"], false, "a closure's local home cannot escape its frame");
    for (name, tag) in [
        ("projected_guard", "Call(closure env unsupported)"),
        ("by_value_array_guard", "Call(closure env unsupported)"),
        ("ordinary_tuple_guard", "Promote(non-scalar &mut local)"),
        ("mutable_once_home_guard", "Promote(non-scalar &mut local)"),
        ("once_home_address_binding_guard", "Promote(non-scalar &mut local)"),
        ("once_home_other_comparison_guard", "Promote(non-scalar &mut local)"),
    ] {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "{name}");
        assert_eq!(found[0]["lowered"], false, "{name}: unsupported semantics must stay refused");
        assert!(found[0]["unsupported"].as_array().unwrap().iter()
            .any(|reason| reason[0] == tag), "{name}: {}", found[0]);
    }
}
