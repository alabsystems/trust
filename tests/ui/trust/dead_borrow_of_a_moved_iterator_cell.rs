//@ needs-trust-verify
//@ edition: 2021
//@ revisions: split_next chars_map_lower
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[split_next] check-pass
//@[chars_map_lower] check-fail
//! **A borrow the lowering leaves dead no longer refuses the bundle (Trust,
//! 2026-09-28).**
//!
//! The bridge models many calls as a havoc without consuming the reference it lowered
//! for their `&`/`&mut` argument. When that reference was a `Borrow`/`BorrowMut`
//! instruction left with no reader, trust-mc's input gate refused the whole bundle over
//! it: an `Alloca` feeding a `BorrowMut` is "not promotable". a7a181adfb added a pass
//! that replaced such a borrow with a stamped havoc. Since B1 (07451d974f, 2026-10-08)
//! the bridge spells every reference as a claim-carrying `Copy` and never emits a
//! permission instruction, so that pass could no longer fire, and BMC-LANE-1
//! (2026-11-06) removed it. These revisions now pin the B1 spelling on the same two
//! programs.
//!
//! * `split_next`: the idiomatic sample's i09. The moved `Split` is spilled to a cell and
//!   `&mut`-borrowed for a `next` the bridge models as a total havoc.
//! * `chars_map_lower`: the ordinary sweep's t33. The closure's spilled `char` is
//!   `&`-borrowed for `to_ascii_lowercase` and is also read for its validity range.

#[cfg(split_next)]
pub fn first_field(line: &str) -> &str {
    line.split(',').next().unwrap_or("")
}

#[cfg(chars_map_lower)]
pub fn as_lower(s: &str) -> String {
    //[chars_map_lower]~^ ERROR Trust Level 0 safety verification incomplete for `dead_borrow_of_a_moved_iterator_cell::as_lower`
    //[chars_map_lower]~^^ ERROR Trust strict verification failed for `dead_borrow_of_a_moved_iterator_cell::as_lower`
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // ZERO-ROW-GATE: the body publishes no row of its own, and its `collect::<String>` over `Map<Chars, _>` (`String::from_iter`)
    // is a call into BUNDLED std bodies, which no registry the gate reads discharges.
    // Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    // SHAPE CHANGE, re-pinned 2026-10-25 for upstream 76456a688bc0: `String::from_iter` now
    // routes through the `FromCharIterSpec` specialization (and `Extend<char>` through
    // `SpecExtendChars`), so the bundled shape mints two obligations (a runtime-checked
    // panic-freedom assert + one skipped) where it minted zero; the L0 gate therefore also
    // reports its own ERROR above the strict one. Executed A/B at gate base 5a5545798bca:
    // the old single-ERROR shape; under plain verify=on the body now builds with the
    // assertion runtime-retained, while certify still refuses on both errors. Nothing
    // formerly proved is unproved (the base profile proved 0 of 0).
    s.chars().map(|c| c.to_ascii_lowercase()).collect()
}
