//! Nested locals and outward loop transfers retain exact SSA state.
//! Concrete cases cover every residue used by the bounded subjects. The
//! compiler's direct-IR interpreter is compared with the original MIR oracle;
//! compiling the original Rust through LLVM alone cannot satisfy this test.
//@ ignore-cross-compile

use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    let output = cmd(rustc_path()).args([
        "subject.rs", "--edition=2024", "--crate-type=lib", "--crate-name=loop_control",
        "--emit=metadata", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
        "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
        "-Ztrust-dump=ir:ir", "-o", "loop_control.rmeta",
    ]).run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"));
    let coverage: serde_json::Value = serde_json::from_slice(
        &rfs::read("ir/loop_control.coverage.json"),
    ).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let families = ["local_nested", "outer_break", "outer_continue",
        "outer_break_value", "three_levels", "mixed_exits"];
    let mut names: Vec<String> = families.iter().map(|name| name.to_string()).collect();
    names.extend(["external_local_nested", "external_outer_break", "external_outer_continue",
        "external_outer_break_value", "shadowed_labels", "bare_outer_break",
        "outer_break_in_else", "outer_continue_in_else"].iter().map(|name| name.to_string()));
    for family in families {
        names.extend((0..8).map(|n| format!("{family}_case_{n}")));
    }
    let rows = coverage["bodies"].as_array().unwrap();
    assert_eq!(rows.len(), names.len() + 1, "every fixture body must be counted");
    let text = trust_ir::by_display_path(&rfs::read_to_string("ir/loop_control.trust-ir.txt"));
    for name in names {
        let found: Vec<_> = rows.iter().filter(|row| row["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "exactly one source body for {name}");
        let row = found[0];
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert_eq!(row["symbolic"], false, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
        let interpreter = &row["differentials"]["interpreter"];
        assert_eq!(interpreter["verdict"], "agreed", "{name}: {row}");
        assert!(interpreter["samples"].as_u64().unwrap() > 0, "{name}: {row}");
        let plain = format!("fn @{name}(");
        let quoted = format!("fn @\"{name}\"(");
        let body = text.split_once(&plain).or_else(|| text.split_once(&quoted))
            .unwrap_or_else(|| panic!("missing emitted IR body {name}")).1
            .split_once("\n}\n").unwrap().0;
        assert!(!body.contains("undef"), "{name}: {body}");
        assert!(body.contains("br ") || body.contains("condbr "), "{name}: {body}");
    }
    // A block's scope must not be accepted as a loop target merely because
    // another loop is open. General outward labeled-block support is separate.
    let negative: Vec<_> = rows.iter()
        .filter(|row| row["def_path"] == "outer_block_is_not_a_loop").collect();
    assert_eq!(negative.len(), 1);
    assert_eq!(negative[0]["lowered"], false);
    assert!(negative[0]["unsupported"].as_array().unwrap().iter()
        .any(|reason| reason[0] == "Break(non-innermost label)"));
}
