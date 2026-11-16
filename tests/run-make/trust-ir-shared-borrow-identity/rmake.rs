//! Shared borrowing must preserve the storage of an already addressable local.
//! In the old producer, increment(&counter) mutated a fresh Counter snapshot,
//! while the next read loaded the original. Two &local arguments after a mutable
//! borrow likewise pointed at different fresh slots. Read the producer's emitted
//! program to check these aliasing relationships; a successful LLVM build alone
//! cannot test the separate direct producer.
//! Whole locals borrowed only through shared references need the same identity.
//! Unsupported storage, duplicated allocations and suspensions must fail closed.
//@ ignore-cross-compile

mod check;

use run_make_support::{rfs, rustc, serde_json};

fn refused_row<'a>(coverage: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    let rows = coverage["bodies"].as_array().expect("complete body inventory");
    let matching: Vec<_> = rows.iter().filter(|row| {
        row["def_path"].as_str().is_some_and(|path| {
            path == name || path.ends_with(&format!("::{name}"))
        })
    }).collect();
    assert_eq!(matching.len(), 1, "one refusal body for {name}: {rows:?}");
    let row = matching[0];
    assert_eq!(row["lowered"], false, "unsupported storage must not lower: {row}");
    assert_eq!(row["spliced"], false, "unsupported storage must not splice: {row}");
    row
}

fn assert_refused(coverage: &serde_json::Value, name: &str, tag: &str) {
    let row = refused_row(coverage, name);
    assert!(row["unsupported"].to_string().contains(tag), "missing {tag}: {row}");
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // The vanilla Rust oracle has no direct Trust-IR artifact interface.
    }
    rustc()
        .input("subject.rs")
        .crate_name("shared_borrow_identity")
        .crate_type("lib")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg("-Ztrust-dump=ir:ir")
        .run();
    check::verify_dump(&rfs::read_to_string("ir/shared_borrow_identity.trust-ir.txt"));

    let output = rustc()
        .input("refusals.rs")
        .crate_name("shared_borrow_refusals")
        .crate_type("lib")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        // Trust: the tracked spelling of the Option-flag lane. Its former environment
        // variable is refused as an untracked control (4f154628a5), so the run aborted.
        .arg("-Ztrust-option-flag-lanes=on")
        .arg("-Ztrust-dump=ir:refusal-ir")
        .run();
    assert!(!output.stderr_utf8().contains("final Trust-IR module validation failed"),
        "storage must be refused before emitting invalid IR");
    let coverage: serde_json::Value = serde_json::from_str(&rfs::read_to_string(
        "refusal-ir/shared_borrow_refusals.coverage.json",
    )).expect("valid refusal coverage JSON");
    for (name, tag) in [
        ("reference_valued_local", "Promote(init is borrow ptr)"),
        ("empty_array_of_references", "Promote(non-scalar &mut local)"),
        ("empty_array_of_opaque_elements", "Promote(non-scalar &mut local)"),
        ("mutable_empty_array_storage", "Promote(non-scalar &mut local)"),
        ("reassigned_wide_parameter", "Promote(non-scalar &mut param)"),
        ("projected_write_wide_parameter", "Promote(non-scalar &mut param)"),
        ("mutable_wide_parameter", "Promote(non-scalar &mut param)"),
        ("reassigned_reference_parameter", "Promote(non-scalar &mut param)"),
        ("raw_const_wide_parameter", "Promote(non-scalar &mut param)"),
        ("projected_borrow_wide_parameter", "Promote(non-scalar &mut param)"),
        ("duplicated_wide_local", "TupleMatch(or-arm body duplicated with promotable local)"),
        ("shared_dyn_parameter", "Borrow(shared local lacks stable storage)"),
        ("escape_reference_parameter", "Promote(non-scalar &mut param)"),
        ("escape_shared_reference_lifetime", "Return(borrow ptr escapes tail)"),
        ("raw_parameter_deref", "Deref(non-borrow ptr)"),
        ("guarded_payload_reference", "Borrow(shared local lacks stable storage)"),
        ("duplicated_arm", "TupleMatch(or-arm body duplicated with promotable local)"),
        ("activation_slot_across_suspend::{closure#0}", "Yield(promoted local across suspend)"),
        ("shared_frame_across_await::{closure#0}", "Yield(shared frame address across suspend)"),
        ("shared_frame_borrowed_after_await::{closure#0}", "Yield(shared frame address across suspend)"),
    ] {
        assert_refused(&coverage, name, tag);
    }
    assert_refused(&coverage, "escape_reference_parameter", "Borrow(shared local lacks stable storage)");
    // These original source bodies now use primitive floating-point homes and
    // typed stores. Keep their source and body identities in the same inventory.
    // Trust: 95c88b6485 (THIR-PRIMITIVE-OWNED-HOMES-1) gives a borrowed by-value primitive
    // destructure leaf its own owned home, so `destructured_local` lowers too. The refusal
    // for reference-valued and aggregate leaves stays pinned by
    // tests/run-make/trust-primitive-owned-storage.
    for name in [
        "mutable_float_storage",
        "raw_mutable_float_storage",
        "mutable_pattern_float_storage",
        "destructured_local",
    ] {
        let rows: Vec<_> = coverage["bodies"].as_array().unwrap().iter()
            .filter(|row| row["def_path"] == name).collect();
        assert_eq!(rows.len(), 1, "one original owned-home storage body: {name}");
        assert_eq!(rows[0]["lowered"], true, "{name}: {}", rows[0]);
        assert_eq!(rows[0]["spliced"], true, "{name}: {}", rows[0]);
        assert!(rows[0]["unsupported"].as_array().unwrap().is_empty(), "{name}: {}", rows[0]);
    }
    // Trust: the integer twin of `raw_parameter_deref` is e0e9606dab's typed raw-entry load.
    let integer = coverage["bodies"].as_array().expect("complete body inventory").iter()
        .find(|row| row["def_path"] == "raw_parameter_integer_deref")
        .expect("raw_parameter_integer_deref row");
    assert_eq!(integer["lowered"], true, "typed integer raw-entry load lowers: {integer}");
    assert!(integer["unsupported"].as_array().is_some_and(|u| u.is_empty()), "{integer}");
}
