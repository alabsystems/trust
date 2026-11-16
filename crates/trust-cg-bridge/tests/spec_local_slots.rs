// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The spec side's BLOCK-LOCAL SLOTS (`verify_output_trust_ir::admit_local_slot` and
//! `LocalSlots`, DECISION_QUEUE SPEC-SLOT-1), through `trust_ir_function_semantics`.
//!
//! An `alloca` whose address is used only by plain loads and stores of its own type in its own
//! block is a fresh cell. The spec reads each load as the latest store before it. Every other
//! `alloca` stays outside the modeled fragment. Each admission condition has a test below that
//! fails when that condition alone is dropped (others may fail too).

use trust_cg_bridge::verify_output_trust_ir::trust_ir_function_semantics;
use trust_ir::value::FuncId;
use trust_types::Formula;

const HEAD: &str = "module \"rung\"\ntarget \"arm64-apple-macosx\" 8 little\n";

/// The spec of `@rung` (function 0), or its refusal. `extra` is appended as further functions,
/// with `functy.1 = (ptr) -> ()` declared for them.
fn spec_with(sig: &str, body: &str, extra: &str) -> Result<Formula, String> {
    let text = format!(
        "{HEAD}functy.0 = {sig}\nfuncty.1 = (ptr) -> ()\nfn @rung(functy.0) {{\n{body}\n}}\n{extra}"
    );
    let module = trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{e:?}\n{text}"));
    trust_ir_function_semantics(&module, FuncId::new(0)).map(|s| s.value)
}

fn spec(sig: &str, body: &str) -> Result<Formula, String> {
    spec_with(sig, body, "")
}

fn refused(sig: &str, body: &str) -> String {
    match spec(sig, body) {
        Ok(v) => panic!("the spec modeled a slot it must refuse: {v:?}\n{body}"),
        Err(e) => e,
    }
}

/// `e` is the admission refusal of slot `%n`.
#[track_caller]
fn not_a_slot(e: &str, n: u32) {
    assert!(e.contains(&format!("`Alloca` %{n} is not a block-local slot")), "{e}");
}

/// s17_ref_local's producer IR (`let mut y = x; y += 5; y`): the spec is
/// `x + 5`, the value the second load reads after the second store.
#[test]
fn a_block_local_slot_reads_its_latest_store() {
    let v = spec(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = const u64 5
    %3 = load u64, ptr %1
    %4 = add u64 %3, %2
    store u64 %4, ptr %1
    %5 = load u64, ptr %1
    ret %5",
    )
    .expect("a block-local slot is modeled");
    let shown = format!("{v:?}");
    assert!(shown.contains("BvAdd"), "the spec is x + 5: {shown}");
    assert!(shown.contains("value: 5"), "the spec is x + 5: {shown}");
}

/// Two slots in one block are two cells: a store to one is not read through
/// the other.
#[test]
fn two_slots_are_two_cells() {
    let v = spec(
        "(u64, u64) -> (u64)",
        "bb0(%0: u64, %1: u64):
    %2 = alloca u64
    %3 = alloca u64
    store u64 %0, ptr %2
    store u64 %1, ptr %3
    %4 = load u64, ptr %2
    ret %4",
    )
    .expect("two block-local slots are modeled");
    let shown = format!("{v:?}");
    assert!(shown.contains("X0") && !shown.contains("X1"), "the spec reads x0 only: {shown}");
}

/// A slot is local to the block that defines it, whichever block that is.
#[test]
fn a_slot_outside_the_entry_block_is_modeled() {
    let v = spec(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    br bb1
bb1:
    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    ret %2",
    )
    .expect("a block-local slot in bb1 is modeled");
    let shown = format!("{v:?}");
    assert!(shown.contains("X0"), "the spec is x: {shown}");
}

#[test]
fn a_load_before_any_store_is_refused() {
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    %2 = load u64, ptr %1
    ret %2",
    );
    assert!(e.contains("load of slot %1 before any store"), "{e}");
    // Another slot being written does not initialize this one.
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    %2 = alloca u64
    store u64 %0, ptr %1
    %3 = load u64, ptr %2
    ret %3",
    );
    assert!(e.contains("load of slot %2 before any store"), "{e}");
}

#[test]
fn a_slot_used_in_another_block_is_refused() {
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    br bb1
bb1:
    %2 = load u64, ptr %1
    ret %2",
    );
    not_a_slot(&e, 1);
    assert!(e.contains("bb1 uses it"), "{e}");
}

/// The refusal names the first foreign block that uses the slot, on every run (a map of
/// blocks iterates in a different order per process and per map).
#[test]
fn a_cross_block_refusal_names_the_first_foreign_block_every_time() {
    let body = "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = icmp eq u64 %0, %0
    condbr %2, bb1, bb2
bb1:
    %3 = load u64, ptr %1
    br bb3
bb2:
    %4 = load u64, ptr %1
    br bb3
bb3:
    %5 = load u64, ptr %1
    ret %5";
    for _ in 0..32 {
        let e = refused("(u64) -> (u64)", body);
        not_a_slot(&e, 1);
        assert!(e.contains("bb1 uses it"), "{e}");
    }
}

#[test]
fn a_slot_whose_address_is_stored_as_a_value_is_refused() {
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    %2 = alloca ptr
    store u64 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load u64, ptr %1
    ret %3",
    );
    not_a_slot(&e, 1);
    // The same store typed as the slot's own type (ill-typed: the value is the address), so
    // only the address-operand condition turns it away.
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    %2 = alloca u64
    store u64 %0, ptr %1
    store u64 %1, ptr %2
    %3 = load u64, ptr %1
    ret %3",
    );
    not_a_slot(&e, 1);
    // The slot's address stored into the slot itself: only `value != slot` turns it away.
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    store u64 %1, ptr %1
    %2 = load u64, ptr %1
    ret %2",
    );
    not_a_slot(&e, 1);
}

#[test]
fn a_slot_whose_address_is_returned_is_refused() {
    let e = refused(
        "(u64) -> (ptr)",
        "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    ret %1",
    );
    not_a_slot(&e, 1);
    assert!(e.contains("`Return` uses it"), "{e}");
}

/// The address escaping into a call, a block argument, a GEP or a drop is refused in the
/// slot's own block, by the use, not by the block.
#[test]
fn a_slot_whose_address_escapes_is_refused() {
    let head = "bb0(%0: u64):\n    %1 = alloca u64\n    store u64 %0, ptr %1\n";
    let g = "fn @g(functy.1) {\nbb0(%0: ptr):\n    ret\n}\n";
    for (what, rest, extra, label) in [
        (
            "a call argument",
            "    call @func.1(%1)\n    %2 = load u64, ptr %1\n    ret %2",
            g,
            "`Call` ",
        ),
        (
            "a GEP base",
            "    %2 = const u64 0\n    %3 = gep u8, ptr %1, %2\n    %4 = load u64, ptr %1\n    ret %4",
            "",
            "`GEP` ",
        ),
        ("a dropped place", "    drop u64, %1\n    %2 = load u64, ptr %1\n    ret %2", "", ""),
    ] {
        let body = format!("{head}{rest}");
        let e = spec_with("(u64) -> (u64)", &body, extra)
            .expect_err(&format!("{what}: the escaped slot was modeled"));
        not_a_slot(&e, 1);
        assert!(e.contains(&format!("{label}uses it other than")), "{what}: {e}");
    }
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    br bb1(%1)
bb1(%2: ptr):
    %3 = load u64, ptr %2
    ret %3",
    );
    not_a_slot(&e, 1);
    assert!(e.contains("`Br` uses it other than"), "a block argument: {e}");
}

#[test]
fn a_slot_read_at_another_type_is_refused() {
    for (load, ret) in [("u32", "u32"), ("i64", "i64")] {
        let e = refused(
            &format!("(u64) -> ({ret})"),
            &format!(
                "bb0(%0: u64):
    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = load {load}, ptr %1
    ret %2"
            ),
        );
        not_a_slot(&e, 1);
    }
}

#[test]
fn a_slot_written_at_another_type_is_refused() {
    for (param, store) in [("u32", "u32"), ("i64", "i64")] {
        let e = refused(
            &format!("({param}) -> (u64)"),
            &format!(
                "bb0(%0: {param}):
    %1 = alloca u64
    store {store} %0, ptr %1
    %2 = load u64, ptr %1
    ret %2"
            ),
        );
        not_a_slot(&e, 1);
    }
}

/// A store annotated with the slot's type whose value is DECLARED another type is refused,
/// as trust-ir's `eval_store` refuses it, rather than reinterpreted at the same width.
#[test]
fn a_stored_value_of_another_declared_type_is_refused() {
    for (param, what) in [("i64", "a signed value"), ("ptr", "a pointer")] {
        let e = refused(
            &format!("({param}) -> (u64)"),
            &format!(
                "bb0(%0: {param}):
    %1 = alloca u64
    store u64 %0, ptr %1
    %2 = load u64, ptr %1
    ret %2"
            ),
        );
        assert!(e.contains("store to slot %1 of %0 declared"), "{what}: {e}");
    }
}

#[test]
fn a_volatile_access_to_a_slot_is_refused() {
    for (store, load) in [("volatile store", "load"), ("store", "volatile load")] {
        let e = refused(
            "(u64) -> (u64)",
            &format!(
                "bb0(%0: u64):
    %1 = alloca u64
    {store} u64 %0, ptr %1
    %2 = {load} u64, ptr %1
    ret %2"
            ),
        );
        not_a_slot(&e, 1);
    }
}

#[test]
fn an_explicitly_aligned_slot_or_access_is_refused() {
    for (alloca, store, load) in [
        ("alloca u64, align 8", "", ""),
        ("alloca u64", ", align 8", ""),
        ("alloca u64", "", ", align 8"),
    ] {
        let e = refused(
            "(u64) -> (u64)",
            &format!(
                "bb0(%0: u64):
    %1 = {alloca}
    store u64 %0, ptr %1{store}
    %2 = load u64, ptr %1{load}
    ret %2"
            ),
        );
        not_a_slot(&e, 1);
    }
}

#[test]
fn an_array_slot_is_refused() {
    let e = refused(
        "(u64) -> (u64)",
        "bb0(%0: u64):
    %1 = const u64 2
    %2 = alloca u64, %1
    store u64 %0, ptr %2
    %3 = load u64, ptr %2
    ret %3",
    );
    not_a_slot(&e, 2);
}

#[test]
fn a_pointer_or_wide_slot_is_refused() {
    let e = refused(
        "(ptr) -> (ptr)",
        "bb0(%0: ptr):
    %1 = alloca ptr
    store ptr %0, ptr %1
    %2 = load ptr, ptr %1
    ret %2",
    );
    assert!(e.contains("pointer slot"), "{e}");
    let e = refused(
        "(u128) -> (u128)",
        "bb0(%0: u128):
    %1 = alloca u128
    store u128 %0, ptr %1
    %2 = load u128, ptr %1
    ret %2",
    );
    assert!(e.contains("128-bit slot"), "{e}");
}

/// A load or store through any pointer that is not a slot stays outside the fragment, beside
/// a slot or alone: the slot model claims only accesses through its own cells.
#[test]
fn an_access_through_another_pointer_is_outside_the_fragment() {
    for (sig, body, inst) in [
        (
            "(ptr, u64) -> (u64)",
            "bb0(%0: ptr, %1: u64):
    %2 = alloca u64
    store u64 %1, ptr %2
    store u64 %1, ptr %0
    %3 = load u64, ptr %2
    ret %3",
            "`Store`",
        ),
        (
            "(ptr, u64) -> (u64)",
            "bb0(%0: ptr, %1: u64):
    store u64 %1, ptr %0
    %2 = load u64, ptr %0
    ret %2",
            "`Store`",
        ),
        (
            "(ptr) -> (u64)",
            "bb0(%0: ptr):
    %1 = load u64, ptr %0
    ret %1",
            "`Load`",
        ),
    ] {
        let e = refused(sig, body);
        assert!(e.contains(&format!("instruction {inst} is outside the modeled fragment")), "{e}");
        assert!(!e.contains("slot"), "{e}");
    }
}
