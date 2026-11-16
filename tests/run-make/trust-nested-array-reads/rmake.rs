//! Nested arrays are values: preserve row copies, bounds, and slice strides.
//! Zero-sized rows must not require allocation provenance after their bounds check.
//@ ignore-cross-compile
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::{
    AssertKind, Inst, Ty,
    binary::deserialize_module,
    interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter},
};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    rfs::write("native.rs", format!("{}\n{}", rfs::read_to_string("subject.rs"),
        rfs::read_to_string("native_assertions.rs")));
    cmd(rustc_path()).args(["native.rs", "--edition=2024", "-Ztrust-verify=off",
        "-Ztrust-ir-lower=off", "-Coverflow-checks=on", "-o", "native"]).run();
    cmd("./native").run();
    for case in ["outer-oob", "inner-oob", "slice-oob", "unit-outer-oob", "unit-inner-oob",
        "empty-outer", "empty-inner", "large-outer", "zst-slice-outer", "zst-slice-inner",
        "zero-len-outer", "direct-adt-oob", "direct-adt-slice-oob"] {
        assert!(cmd("./native").arg(case).run_fail().stderr_utf8().contains("index out of bounds"), "{case}");
    }
    assert!(cmd("./native").arg("drop").run_fail().stderr_utf8().contains("drop ran"));
    cmd(rustc_path()).args(["subject.rs", "--edition=2024", "--crate-type=lib",
        "--crate-name=nested_arrays", "--emit=metadata", "-Copt-level=0", "-Coverflow-checks=on",
        "-Zthreads=1", "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        "-Ztrust-dump=ir:ir", "-o", "subject.rmeta"]).run();
    let report: serde_json::Value = serde_json::from_slice(&rfs::read("ir/nested_arrays.coverage.json")).unwrap();
    assert_eq!(report["proof_authority"], false);
    assert_eq!(report["native_verification_requests"], false);
    assert_eq!(report["direct_obligation_capability"], "obligation-bearing-pending-v2");
    let rows = report["bodies"].as_array().unwrap();
    let mut expected = vec![
        "nested_const",
        "nested_dynamic",
        "nested_row",
        "nested_row::{constant#0}",
        "nested_param",
        "nested_param::{constant#0}",
        "nested_param::{constant#1}",
        "nested_slice",
        "nested_slice::{constant#0}",
        "nested_index_returns",
        "nested_base_returns",
        "nested_unit",
        "nested_unit::{constant#0}",
        "nested_unit::{constant#1}",
        "copied_row",
        "changed_place",
        "captured_value",
        "changed_slice",
        "changed_slice::{constant#0}",
        "captured_slice",
        "captured_slice::{constant#0}",
        "captured_slice::{constant#1}",
        "reference_row",
        "reference_row::{constant#0}",
        "reference_row::{constant#1}",
        "pointer_leaf_refused",
        "generic_length",
        "generic_length::{constant#1}",
        "<Bomb as std::ops::Drop>::drop",
        "drop_leaf_refused",
        "empty_rows",
        "empty_rows::{constant#0}",
        "empty_rows::{constant#1}",
        "empty_inner",
        "empty_inner::{constant#0}",
        "empty_inner::{constant#1}",
        "large_zst_row",
        "large_zst_row::{constant#0}",
        "large_zst_row::{constant#1}",
        "param_values",
        "slice_values",
        "reference_values",
        "row_value",
        "nested_float",
        "nested_double",
        "nested_char",
        "nested_bool",
        "deep",
        "empty_slice",
        "rectangular",
        "rectangular_slice",
        "rectangular_slice::{constant#0}",
        "zst_slice_rows",
        "zst_slice_rows::{constant#0}",
        "zst_slice_values",
        "zst_slice_values::{constant#0}",
        "zst_slice_values::{constant#1}",
        "zero_len_slice",
        "zero_len_slice::{constant#0}",
        "zero_len_values",
        "direct_adt",
        "direct_adt_slice",
        "nested_adt_refused",
        "<Plain as std::clone::Clone>::clone"
    ];
    let mut observed: Vec<_> = rows.iter().map(|r| r["def_path"].as_str().unwrap()).collect();
    expected.sort(); observed.sort(); assert_eq!(observed, expected);
    for row in rows {
        let name = row["def_path"].as_str().unwrap();
        let refused = ["pointer_leaf_refused", "generic_length", "drop_leaf_refused", "nested_adt_refused"].contains(&name);
        assert_eq!(row["lowered"], !refused, "{name}: {row}");
        assert_eq!(row["spliced"], !refused, "{name}: {row}");
        assert_eq!(row["symbolic"], name == "generic_length", "{name}: {row}");
        assert_eq!(row["unsupported"].as_array().unwrap().is_empty(), !refused, "{name}: {row}");
        if refused {
            let tag = if name == "generic_length" {
                "Index(const index over non-constant array length)"
            } else {
                "Index(non-scalar element ty)"
            };
            assert!(row["unsupported"].as_array().unwrap().iter().any(|r| r[0] == tag), "{name}: {row}");
        }
    }
    assert_eq!(report["totals"]["bodies"], 64);
    assert_eq!(report["totals"]["lowered"], 60);
    assert_eq!(report["totals"]["spliced"], 60);
    assert_eq!(report["totals"]["symbolic"], 1);
    let module = deserialize_module(&rfs::read("ir/nested_arrays.trust-ir.bin")).unwrap();
    // Match each emitted bounds assertion to exactly one pending obligation at
    // the same instruction. Runtime traps alone do not establish this coverage.
    let text = rfs::read_to_string("ir/nested_arrays.trust-ir.txt");
    let obligations: Vec<_> = text.lines().filter(|line| line.starts_with("obligation ")
        && line.contains(" bounds_check ")).collect();
    let mut sites = std::collections::BTreeSet::new();
    for function in &module.functions {
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                if matches!(&node.inst, Inst::Assert { kind: AssertKind::BoundsCheck { .. }, .. }) {
                    let site = format!("site f{}/bb{}#{index}", function.id, block.id);
                    assert!(sites.insert(site.clone()), "duplicate bounds site {site}");
                    let matching: Vec<_> = obligations.iter().filter(|line| line.ends_with(site.as_str())).collect();
                    assert_eq!(matching.len(), 1, "{site}: missing/duplicate pending obligation");
                    assert!(matching[0].contains(" bounds_check pending "), "{site}: {}", matching[0]);
                    assert!(matching[0].contains("trust-thir-lower/direct-assert@1"), "{site}");
                }
            }
        }
    }
    assert_eq!(obligations.len(), sites.len(), "orphaned bounds obligation");
    let interpreter = Interpreter::with_module(&module);
    let function = |name: &str| {
        let fs: Vec<_> = module.functions.iter().filter(|f| f.display_path.as_deref() == Some(name)).collect();
        assert_eq!(fs.len(), 1, "{name}"); fs[0]
    };
    for (name, expected) in [
        ("nested_const", 2), ("nested_dynamic", 2), ("nested_row", 1), ("nested_param", 2),
        ("nested_slice", 2), ("nested_unit", 2), ("deep", 3), ("rectangular", 2),
        ("zst_slice_rows", 2), ("zero_len_slice", 1), ("empty_inner", 2),
        ("empty_rows", 1), ("large_zst_row", 1), ("nested_index_returns", 0),
        ("nested_base_returns", 0), ("direct_adt", 1), ("direct_adt_slice", 1),
    ] {
        let count = function(name).blocks.iter().flat_map(|b| &b.body)
            .filter(|n| matches!(&n.inst, Inst::Assert { kind: AssertKind::BoundsCheck { .. }, .. })).count();
        assert_eq!(count, expected, "{name}: changed bounds coverage");
    }
    let u = |n| InterpretValue::int(Ty::Usize, n).unwrap();
    let check = |name: &str, args: Vec<InterpretValue>, expected: i128| {
        let result = interpreter.execute_func(function(name).id, args).unwrap();
        assert_eq!(result.host_calls, 0, "{name}");
        assert_eq!(result.returns, vec![InterpretValue::int(Ty::U32, expected).unwrap()], "{name}");
    };
    check("nested_const", vec![], 3);
    for (i, value) in [(0,13),(1,29)] {
        check("direct_adt", vec![u(i)], value);
        check("direct_adt_slice", vec![u(i)], value);
    }
    check("nested_index_returns", vec![], 7);
    check("nested_base_returns", vec![], 7);
    check("nested_char", vec![u(0)], 'a' as i128);
    check("nested_char", vec![u(1)], '🙂' as i128);
    for i in 0..2 {
        check("empty_rows", vec![u(i)], 0);
        check("large_zst_row", vec![u(i)], 1_048_576);
        check("zero_len_values", vec![u(i)], 0);
        for j in 0..2 {
            let value = 1 + 2*i+j;
            for name in ["nested_dynamic", "copied_row", "captured_value", "captured_slice",
                "param_values", "slice_values", "reference_values", "row_value", "nested_float", "nested_double"] {
                check(name, vec![u(i),u(j)], value);
            }
            for name in ["changed_place", "changed_slice"] { check(name, vec![u(i),u(j)], value+4); }
            for name in ["nested_unit", "zst_slice_values"] { check(name, vec![u(i),u(j)], 7); }
            check("nested_bool", vec![u(i),u(j)], i128::from(i!=j));
            for k in 0..2 { check("deep", vec![u(i),u(j),u(k)], 1+4*i+2*j+k); }
        }
        for j in 0..3 {
            for name in ["rectangular", "rectangular_slice"] { check(name, vec![u(i),u(j)], 1+3*i+j); }
        }
    }
    for (name, args, operands) in [
        ("direct_adt", vec![u(2)], [2,2]),
        ("direct_adt_slice", vec![u(2)], [2,2]),
        ("nested_dynamic", vec![u(99),u(0)], [99,2]),
        ("nested_dynamic", vec![u(0),u(17)], [17,2]),
        ("empty_slice", vec![], [0,0]),
        ("nested_unit", vec![u(2),u(0)], [2,2]),
        ("nested_unit", vec![u(0),u(2)], [2,2]),
        ("empty_rows", vec![u(2)], [2,2]),
        ("empty_inner", vec![u(0)], [0,0]),
        ("large_zst_row", vec![u(2)], [2,2]),
        ("zst_slice_values", vec![u(2),u(0)], [2,2]),
        ("zst_slice_values", vec![u(0),u(2)], [2,2]),
        ("zero_len_values", vec![u(2)], [2,2]),
    ] {
        let error = interpreter.execute_func(function(name).id, args).unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::Panic, "{name}: {error:?}");
        assert_eq!(error.panic.unwrap().operands, Some(operands), "{name}");
    }
    // These mirror the native non-null, aligned dangling slices above. No allocation
    // exists to satisfy a hidden zero-byte Load; only the bounds-checked value can run.
    for (name, address, two_indices, expected) in [
        ("zst_slice_rows", 1, true, 7), ("zero_len_slice", 4, false, 0),
    ] {
        let f = function(name);
        let ty = module.func_types[f.ty.as_usize()].params[0].clone();
        let slice = InterpretValue { ty, kind: InterpretValueKind::FatPtr {
            data: Box::new(InterpretValue { ty: Ty::Ptr, kind: InterpretValueKind::DanglingPtr(address) }),
            metadata: Box::new(InterpretValue::int(Ty::U64, 2).unwrap()),
        }};
        let mut args=vec![slice.clone(),u(0)]; if two_indices { args.push(u(0)); }
        check(name,args,expected);
        let mut args=vec![slice,u(2)]; if two_indices { args.push(u(0)); }
        let error=interpreter.execute_func(f.id,args).unwrap_err();
        assert_eq!(error.code,InterpretErrorCode::Panic,"{name}: {error:?}");
        assert_eq!(error.panic.unwrap().operands,Some([2,2]),"{name}");
    }
    for name in ["nested_const", "nested_dynamic", "nested_row", "nested_param"] {
        assert!(function(name).blocks.iter().flat_map(|b| &b.body)
            .any(|n| matches!(&n.inst, Inst::ExtractElement { ty: Ty::Array(..), .. })), "{name}");
    }
    assert!(function("nested_slice").blocks.iter().flat_map(|b| &b.body)
        .any(|n| matches!(&n.inst, Inst::Load { ty: Ty::Array(..), .. })));
}
