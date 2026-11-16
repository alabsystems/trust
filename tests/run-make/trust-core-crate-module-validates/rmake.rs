//! `core`'s analysis-time crate module VALIDATES, so probe channel C sees `core` bodies as
//! spliced (docs/KNOWN_HAZARDS.md, "`core`'s analysis-time crate module still fails final
//! validation", OPEN 2026-10-05; closed 2026-10-13).
//!
//! Before the fix the module failed final validation with four producer defects —
//! `CallArgTypeMismatch` in `<*const [T]>::len` (`ptr::metadata::metadata` declared thin,
//! passed a `*const [T]`) and in a `Hash::hash` caller (a `&str` into a thin `&Self` slot),
//! `CallIndirectArgTypeMismatch` in `fmt::rt::Argument::fmt` and `OperandTypeMismatch` in
//! `fmt::rt::Argument::as_u16` (an opaque-lane carrier used as a fn pointer, a call argument and
//! a `Some` payload) — so `failed_semantic_finalization` published nothing of `core`: channel C
//! read `thir_ok=0` with 353 `assembly-refused(unpublished)` rows (measured on stage 1 of
//! `748592d562`). The first two are refused at the havoc call site (HAVOC-SITE-DST-1,
//! `tests/ui/trust/trust_ir_lower_havoc_dst_site_refused.rs`), the last two at the carrier's
//! typed sinks (OPAQUE-CARRIER-SINKS-1,
//! `tests/ui/trust/trust_ir_lower_opaque_carrier_value_sinks.rs`).
//! After: `thir_ok=320`, no `unpublished` row, no finalization warning.
//!
//! This is the whole-crate pin: a NEW producer defect anywhere in `core` that invalidates the
//! module fails it, with the validator's own message in the panic. Counts other than "some
//! `core` body is spliced" are not pinned — they move with `core` and with every producer lane.
//@ ignore-cross-compile

use run_make_support::{rustc, source_root};

fn main() {
    let out = rustc()
        .edition("2024")
        .crate_type("rlib")
        .input(source_root().join("library/core/src/lib.rs"))
        .sysroot("fakeroot")
        .arg("-Copt-level=3")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Zno-steal-thir")
        .arg("-Ztrust-instance-flip-probe=*")
        .run();
    let stderr = out.stderr_utf8();
    for line in stderr.lines() {
        assert!(
            !line.contains("semantic finalization failed"),
            "`core`'s crate module must validate:\n{line}"
        );
    }
    let unpublished =
        stderr.lines().filter(|l| l.contains("result=assembly-refused(unpublished)")).count();
    assert_eq!(unpublished, 0, "no `core` row may read `assembly-refused(unpublished)`");
    let summary = stderr
        .lines()
        .find(|l| l.starts_with("TRUST-WALLA-PROBE C summary"))
        .unwrap_or_else(|| panic!("channel C printed no summary:\n{stderr}"));
    let thir_ok: usize = summary
        .split_whitespace()
        .find_map(|kv| kv.strip_prefix("thir_ok="))
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("no thir_ok in summary: {summary}"));
    assert!(thir_ok > 0, "`core` must have spliced bodies in channel C: {summary}");
}
