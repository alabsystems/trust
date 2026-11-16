//! A loop's carried state includes assignments hidden in runtime values.
//! Check concrete semantics and retain the unsupported unbound-local case.
//@ ignore-cross-compile
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::Ty;
use trust_ir::reference::binary::deserialize_module;
use trust_ir::reference::interpret::{InterpretValue, Interpreter};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let output = cmd(rustc_path())
        .args([
            "subject.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=loop_values",
            "--emit=metadata",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir",
            "-o",
            "loop_values.rmeta",
        ])
        .run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/loop_values.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    let names = [
        "direct",
        "tuple",
        "array",
        "repeat",
        "adt",
        "borrow",
        "deref",
        "iflet",
        "tuple_local",
        "array_predeclared_local",
        "shadowed_names",
        "nested_field_loop",
        "fru_base_effect",
        "field_effect_order",
        "repeat_evaluates_once",
        "condition_tuple_field",
        "repeat::{constant#0}",
        "repeat_evaluates_once::{constant#0}",
    ];
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len() + 2, "{rows:?}");
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/loop_values.trust-ir.txt"));
    for name in names {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "{name}: {rows:?}");
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        assert_eq!(row["differentials"]["interpreter"]["verdict"], "agreed", "{name}: {row}");
        assert!(
            row["differentials"]["interpreter"]["samples"].as_u64().unwrap() > 0,
            "{name}: {row}"
        );
        // Constant body coverage names the source constant; its emitted
        // initializer is a distinct function with an explicit suffix.
        let ir_name = if name.ends_with("::{constant#0}") {
            format!("{name}::{{const-init}}")
        } else {
            name.to_owned()
        };
        let plain = format!("fn @{ir_name}(");
        let quoted = format!("fn @\"{ir_name}\"(");
        let body = text
            .split_once(&plain)
            .or_else(|| text.split_once(&quoted))
            .unwrap_or_else(|| panic!("missing exact emitted body {ir_name}"))
            .1
            .split_once("\n}\n")
            .expect("complete emitted body")
            .0;
        assert!(!body.contains("undef"), "{name}: {body}");
    }
    // Guard writes now use stable storage. The MIR comparison still cannot
    // model its shallow fake borrow, so check the emitted IR against native
    // execution directly without upgrading that comparison's verdict.
    let guard: Vec<_> = rows.iter().filter(|row| row["def_path"] == "guarded_match").collect();
    assert_eq!(guard.len(), 1);
    assert_eq!(guard[0]["lowered"], true, "{}", guard[0]);
    assert_eq!(guard[0]["symbolic"], false, "{}", guard[0]);
    assert!(guard[0]["unsupported"].as_array().unwrap().is_empty(), "{}", guard[0]);
    assert_eq!(guard[0]["differentials"]["interpreter"]["verdict"], "not-run");
    rfs::write(
        "native.rs",
        format!(
            "{}\nfn main() {{ assert_eq!(guarded_match(), 3); }}\n",
            rfs::read_to_string("subject.rs"),
        ),
    );
    cmd(rustc_path())
        .args([
            "native.rs",
            "--edition=2024",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on",
            "-o",
            "native",
        ])
        .run();
    cmd("./native").run();
    let module = deserialize_module(&rfs::read("ir/loop_values.trust-ir.bin")).unwrap();
    let functions: Vec<_> = module
        .functions
        .iter()
        .filter(|function| function.display_path.as_deref() == Some("guarded_match"))
        .collect();
    assert_eq!(functions.len(), 1);
    let result = Interpreter::with_module(&module).execute_func(functions[0].id, vec![]).unwrap();
    assert_eq!(result.host_calls, 0);
    assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, 3).unwrap()]);
    for (name, reason) in [("uninitialized_external_tuple", "Loop(carried local unbound pre-loop)")]
    {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1);
        assert_eq!(found[0]["lowered"], false, "{name}: {}", found[0]);
        assert!(
            found[0]["unsupported"].as_array().unwrap().iter().any(|r| r[0] == reason),
            "{name}: {}",
            found[0]
        );
    }
}
