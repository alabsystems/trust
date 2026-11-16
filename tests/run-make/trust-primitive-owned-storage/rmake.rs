//! Complete actual-source population, with independent execution in the probe bin.
//@ ignore-cross-compile
use run_make_support::{rfs, rustc, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    rfs::create_dir("primitive-ir");
    rustc().input("subject.rs").crate_name("primitive_owned_storage")
        .crate_type("lib").edition("2021").emit("trust-ir").out_dir("primitive-ir")
        .arg("-Ztrust-verify=off").run();
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "primitive-ir/primitive_owned_storage.trust-ir.coverage.json")).unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    let names = ["store_bool",
        "delayed_bool",
        "tuple_bool",
        "nested_bool",
        "identity_char",
        "delayed_char",
        "tuple_char",
        "nested_char",
        "store_i8",
        "delayed_i8",
        "tuple_i8",
        "nested_i8",
        "store_i16",
        "delayed_i16",
        "tuple_i16",
        "nested_i16",
        "store_i32",
        "delayed_i32",
        "tuple_i32",
        "nested_i32",
        "store_i64",
        "delayed_i64",
        "tuple_i64",
        "nested_i64",
        "store_i128",
        "delayed_i128",
        "tuple_i128",
        "nested_i128",
        "store_isize",
        "delayed_isize",
        "tuple_isize",
        "nested_isize",
        "store_u8",
        "delayed_u8",
        "tuple_u8",
        "nested_u8",
        "store_u16",
        "delayed_u16",
        "tuple_u16",
        "nested_u16",
        "store_u32",
        "delayed_u32",
        "tuple_u32",
        "nested_u32",
        "store_u64",
        "delayed_u64",
        "tuple_u64",
        "nested_u64",
        "store_u128",
        "delayed_u128",
        "tuple_u128",
        "nested_u128",
        "store_usize",
        "delayed_usize",
        "tuple_usize",
        "nested_usize",
        "store_f32",
        "delayed_f32",
        "tuple_f32",
        "nested_f32",
        "store_f64",
        "delayed_f64",
        "tuple_f64",
        "nested_f64",
        "identity_unit",
        "delayed_unit",
        "tuple_unit",
        "nested_unit",
        "struct_i32",
        "array_i32",
        "parameter_bool", "parameter_char", "parameter_i8", "parameter_i16", "parameter_i32", "parameter_i64", "parameter_i128", "parameter_isize", "parameter_u8", "parameter_u16", "parameter_u32", "parameter_u64", "parameter_u128", "parameter_usize", "parameter_f32", "parameter_f64", "parameter_unit"];
    assert_eq!(names.len(), 87);
    assert_eq!(rows.len(), names.len(), "no source-body exclusions");
    for key in ["bodies", "lowered", "spliced"] { assert_eq!(coverage["totals"][key], 87); }
    for key in ["symbolic", "initializer_bodies"] { assert_eq!(coverage["totals"][key], 0); }
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for name in names {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "exact original body {name}");
        assert_eq!(found[0]["lowered"], true, "{name}: {}", found[0]);
        assert_eq!(found[0]["spliced"], true, "{name}: {}", found[0]);
        assert!(found[0]["unsupported"].as_array().unwrap().is_empty(), "{name}: {}", found[0]);
    }
    let text = rfs::read_to_string("primitive-ir/primitive_owned_storage.trust-ir.txt");
    assert!(!text.contains(" = undef "), "never fabricate an initializer");

    rfs::create_dir("primitive-refusal-ir");
    rustc().input("refusals.rs").crate_name("primitive_owned_refusals")
        .crate_type("lib").edition("2021").emit("trust-ir").out_dir("primitive-refusal-ir")
        .arg("-Ztrust-verify=off").run();
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "primitive-refusal-ir/primitive_owned_refusals.trust-ir.coverage.json")).unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), 5);
    assert_eq!(coverage["totals"]["bodies"], 5);
    for key in ["lowered", "spliced", "symbolic", "initializer_bodies"] {
        assert_eq!(coverage["totals"][key], 0);
    }
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    for (name, tag) in [("reference_slot", "LetTuple(promoted binding)"),
        ("aggregate_slot", "LetTuple(promoted binding)"),
        ("char_parameter_store", "Assign(*r= non-mut-borrow ptr)"),
        ("unit_parameter_store", "Assign(*r= non-mut-borrow ptr)"),
        ("unit_indirect_store", "Assign(*r= non-scalar)")]
    {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "exact refusal body {name}");
        assert_eq!(found[0]["lowered"], false);
        assert_eq!(found[0]["spliced"], false);
        assert!(found[0]["unsupported"].to_string().contains(tag),
            "{name}: {}", found[0]);
    }
}
