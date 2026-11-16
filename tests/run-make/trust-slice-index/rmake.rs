//! Actual compiler artifact regression, not source refinement or G1-G8 evidence.
//! Slice metadata bounds differ from allocation bounds. Local place contents are
//! read after the index, but an effectful base expression runs once before it.
//! Independent allocation-backed execution controls live in the compiler's
//! slice_index_tests module and consume freshly emitted binary modules.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn function<'a>(text: &'a str, name: &str) -> &'a str {
    // WS5.2: `Function.name` is the link-time symbol; the def path is the display path.
    let needle = format!("; #display-path: {name:?}\n");
    assert_eq!(text.matches(&needle).count(), 1, "missing/duplicate {name}");
    let (_, body) = text.split_once(&needle).unwrap();
    body.split_once("\n}\n").unwrap().0
}

fn check_slice(body: &str) {
    assert_eq!(body.matches("ptr_metadata ").count(), 1);
    assert_eq!(body.matches("assert ").count(), 1);
    assert_eq!(body.matches("#proof: in_bounds").count(), 1);
    let mut cursor = 0;
    for instruction in [
        "ptr_metadata ",
        "bitcast ",
        "icmp ult usize ",
        "assert ",
        "ptr_data ",
        "gep u8,",
        "load u8,",
    ] {
        cursor += body[cursor..]
            .find(instruction)
            .unwrap_or_else(|| panic!("missing/out-of-order {instruction}: {body}"))
            + instruction.len();
    }
}

fn compile(
    file: &str,
    crate_name: &str,
    count: usize,
    names: &[&str],
    obligations: usize,
) -> String {
    let directory = format!("{crate_name}-ir");
    cmd(rustc_path())
        .args([
            file,
            "--edition=2024",
            "--crate-type=lib",
            &format!("--crate-name={crate_name}"),
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            &format!("-Ztrust-dump=ir:{directory}"),
            "-o",
            &format!("{crate_name}.mir"),
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read(format!("{directory}/{crate_name}.coverage.json")))
            .unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(names.len(), count, "the expected source roster must be complete");
    assert_eq!(rows.len(), count, "all computational siblings stay counted");
    assert_eq!(coverage["totals"]["bodies"].as_u64(), Some(count as u64));
    assert_eq!(coverage["proof_authority"].as_bool(), Some(false));
    assert_eq!(coverage["native_verification_requests"].as_bool(), Some(false));
    assert_eq!(coverage["direct_obligation_capability"], "obligation-bearing-pending-v2");
    let mut refused = 0;
    let mut unsupported = 0;
    for name in names {
        let matching: Vec<_> = rows.iter().filter(|row| row["def_path"] == *name).collect();
        assert_eq!(matching.len(), 1, "missing/duplicate source row {name}");
        let row = matching[0];
        let expected = match *name {
            "write_slice" => serde_json::json!([["Assign(non-local place)", 1]]),
            "reseat_through_alias" => serde_json::json!([
                ["Assign(*r= ptr no value)", 1], ["Borrow(&mut slot missing)", 1],
                ["Promote(non-scalar &mut local)", 1], ["SliceIndex(unsupported slice value)", 1],
                ["VarRef(promoted slot missing)", 1], ["VarRef(unbound)", 1],
            ]),
            _ => serde_json::json!([]),
        };
        let admitted = expected.as_array().unwrap().is_empty();
        refused += usize::from(!admitted);
        unsupported += expected.as_array().unwrap().len();
        assert_eq!(row["kind"], if name.contains("::{constant#") { "const-init" } else { "fn" });
        assert_eq!(row["lowered"], admitted, "{name}");
        assert_eq!(row["spliced"], admitted, "{name}");
        assert_eq!(row["symbolic"], false, "{name}");
        assert_eq!(row["unsupported"], expected, "{name}");
    }
    assert_eq!(coverage["totals"]["lowered"], count - refused);
    assert_eq!(coverage["totals"]["spliced"], count - refused);
    assert_eq!(coverage["totals"]["unsupported"], unsupported);
    assert_eq!(coverage["totals"]["symbolic"], 0);
    assert_eq!(coverage["totals"]["initializer_bodies"],
        names.iter().filter(|name| name.contains("::{constant#")).count());
    let text = rfs::read_to_string(format!("{directory}/{crate_name}.trust-ir.txt"));
    for name in names.iter().filter(|name| matches!(**name, "write_slice" | "reseat_through_alias")) {
        assert!(!text.contains(&format!("; #display-path: {name:?}\n")), "refused body {name} published");
    }
    let claims: Vec<_> = text.lines().filter(|line| line.starts_with("obligation ")).collect();
    assert_eq!(claims.len(), obligations);
    assert!(claims.iter().all(|line| line.contains(" pending ") && line.contains(" site f")));
    for name in names.iter().filter(|name| {
        matches!(
            **name,
            "read_slice"
                | "read_zst"
                | "read_array"
                | "reseat_index"
                | "index_value_is_captured"
                | "call_base_is_captured"
                | "base_effect_precedes_index"
        )
    }) {
        let row = rows.iter().find(|row| row["def_path"] == *name).unwrap();
        assert_eq!(row["lowered"].as_bool(), Some(true), "regressed {name}");
        assert_eq!(row["spliced"].as_bool(), Some(true), "missing body {name}");
        assert_eq!(row["symbolic"].as_bool(), Some(false));
        assert!(row["unsupported"].as_array().unwrap().is_empty());
    }
    text
}

fn main() {
    // Stock-rustc replay has no Trust-IR artifact interface. This is a Trust
    // producer test, not an exclusion from the Rust language compatibility suite.
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let bounds = compile(
        "bounds.rs",
        "slice_bounds_actual",
        5,
        &["read_slice", "read_array", "read_zst", "write_slice", "read_array::{constant#0}"],
        3,
    );
    check_slice(function(&bounds, "read_slice"));
    let array = function(&bounds, "read_array");
    assert_eq!(array.matches("#proof: in_bounds").count(), 1);
    assert!(array.find("assert ").unwrap() < array.find("extractelement ").unwrap());
    let place = compile(
        "place_order.rs",
        "slice_place_order",
        2,
        &["reseat_index", "index_value_is_captured"],
        2,
    );
    for name in ["reseat_index", "index_value_is_captured"] {
        check_slice(function(&place, name));
    }
    let reseat = function(&place, "reseat_index");
    for projection in ["ptr_metadata ", "ptr_data "] {
        let line = reseat.lines().find(|line| line.contains(projection)).unwrap();
        let suffix = if projection == "ptr_metadata " { " %1 to u64" } else { " %1" };
        assert!(line.split("  ;").next().unwrap().ends_with(suffix), "must read b: {line}");
    }
    let effect = compile(
        "effect_order.rs",
        "slice_effect_order",
        6,
        &[
            "reseat_through_alias",
            "choose",
            "call_base_is_captured",
            "base_effect_precedes_index",
            "counted",
            "call_base_runs_once",
        ],
        4,
    );
    for name in ["call_base_is_captured", "base_effect_precedes_index"] {
        let body = function(&effect, name);
        check_slice(body);
        assert_eq!(body.matches("call @").count(), 1, "base call repeated");
        assert!(body.find("call @").unwrap() < body.find("ptr_metadata ").unwrap());
    }
    let coverage: serde_json::Value = serde_json::from_slice(&rfs::read(
        "slice_effect_order-ir/slice_effect_order.coverage.json",
    )).unwrap();
    let rows = coverage["bodies"].as_array().unwrap();
    let id = |name| rows.iter().find(|row| row["def_path"] == name).unwrap()["func_id"]
        .as_u64().unwrap();
    for (name, kind) in [
        ("call_base_is_captured", "bounds_check"),
        ("base_effect_precedes_index", "bounds_check"),
        ("counted", "arithmetic_safety"),
        ("call_base_runs_once", "bounds_check"),
    ] {
        let owner = format!(" function {} source ", id(name));
        let claims: Vec<_> = effect.lines().filter(|line| line.starts_with("obligation ")
            && line.contains(&owner)).collect();
        assert_eq!(claims.len(), 1, "one obligation for {name}");
        assert_eq!(claims[0].split_whitespace().nth(2), Some(kind));
    }
    check_counted_base_once(function(&effect, "call_base_runs_once"), id("counted"));
}

// The newly admitted base call receives the real counter slot. Its single
// effect runs before the index is loaded; that load controls bounds and GEP.
fn check_counted_base_once(body: &str, counted: u64) {
    check_slice(body);
    let lines: Vec<_> = body.lines().map(|line| line.split("  ;").next().unwrap().trim()).collect();
    let definition = |operation: &str| {
        let found: Vec<_> = lines.iter().enumerate().filter_map(|(i, line)| {
            let (value, op) = line.split_once(" = ")?;
            (op == operation).then_some((i, value))
        }).collect();
        assert_eq!(found.len(), 1, "one definition of {operation}: {body}");
        found[0]
    };
    let (zero_at, zero) = definition("const usize 0");
    let (slot_at, slot) = definition("alloca usize");
    let stores: Vec<_> = lines.iter().enumerate().filter(|(_, line)|
        **line == format!("store usize {zero}, ptr {slot}")).collect();
    assert_eq!(stores.len(), 1);
    assert_eq!(body.matches("call @").count(), 1);
    let (call_at, base) = definition(&format!("call @func.{counted}(%0, {slot})"));
    let (index_at, index) = definition(&format!("load usize, ptr {slot}"));
    let (metadata_at, metadata) = definition(&format!("ptr_metadata fatptr<slice ty.0> {base} to u64"));
    let (len_at, len) = definition(&format!("bitcast u64 {metadata} to usize"));
    let (compare_at, compare) = definition(&format!("icmp ult usize {index}, {len}"));
    let assertion_at = lines.iter().position(|line|
        *line == format!("assert {compare}, bounds_check {index}, {len}")).unwrap();
    let (data_at, data) = definition(&format!("ptr_data fatptr<slice ty.0> {base}"));
    let (gep_at, gep) = definition(&format!("gep u8, ptr {data}, {index}"));
    let (load_at, _) = definition(&format!("load u8, ptr {gep}"));
    let order = [zero_at, slot_at, stores[0].0, call_at, index_at, metadata_at,
        len_at, compare_at, assertion_at, data_at, gep_at, load_at];
    assert!(order.windows(2).all(|pair| pair[0] < pair[1]), "effect/index/bounds order: {body}");
}
