#![crate_type = "lib"]
// `contract_panic` is a TOOL attribute: register the `trust` tool namespace so
// the fixture refutes on the REAL unused-annotation row, not vacuously via
// E0433 (see proved/contract_panic_annotated.rs).
#![feature(register_tool)]
#![register_tool(trust)]
// T9 (contract-panic annotation surface) — UNUSED-annotation mutant: the
// `contract_panic` annotation's `message_contains` payload matches NO panic
// call in the function (the function is panic-free). An annotation on
// panic-free code is an ERROR, not a dormant no-op: left standing, it would
// silently absorb the FIRST future panic whose message happens to contain the
// payload — an unaudited reclassification channel. trust-vcgen therefore
// mints an always-SAT (`Bool(true)`) refute-lane VC carrying the
// contract-panic-unused marker, which lands as a guaranteed FAILED row
// (`contract-panic-unused` — dash, not the `contract-panic:` colon prefix, so
// targo counts it as a genuine failure, never a conditional pass). MUST FAIL
// (exit 1) under the default strict policy; the twin proved/ fixture
// (contract_panic_annotated.rs) shows the same annotation verifying cleanly
// when its panic actually exists.

/// Panic-free: the capacity case saturates instead of panicking, so the
/// annotation below can never match anything.
#[trust::contract_panic(message_contains = "capacity is")]
pub fn saturating_slot(len: usize) -> usize {
    if len >= 8 { 7 } else { len }
}
