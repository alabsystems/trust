//@ needs-trust-verify
//@ revisions: marker test_case_runner test_case_default_runner
//@ compile-flags: --test -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-verify-output=both
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: excluded:test-harness-synthesized
//~? RAW Trust: NOT EXCLUDED [test-harness-synthesized] `test_harness_exclusion_not_spoofable::main` (harness-main)
//! Trust (CB4): the libtest-harness exclusion cannot be minted from source.
//!
//! It is keyed on PROVENANCE — the expansion that produced each item's own span
//! (`rustc_middle::middle::trust_test_harness`) — never on a name and never on
//! `#[rustc_test_marker]` alone, because that attribute is writable (MEASURED:
//! the pre-CB4 `-Ztrust-ir-lower=strict` exemption keyed on it and was fooled by
//! both shapes below). In every revision NO body is excluded — `forbid-output`
//! pins that no `excluded:test-harness-synthesized` row exists at all — and the
//! harness `main` is verified, saying why:
//!
//! * `marker`: a hand-written `#[rustc_test_marker]` `TestDescAndFn` const whose
//!   closure overflows and casts a borrow. The closure is the author's code
//!   (root syntax context), so it is verified; and `main` would run it, so
//!   `main` is not excluded either ("the crate has a `#[test_case]` or
//!   hand-written `#[rustc_test_marker]` item").
//! * `test_case_runner`: `custom_test_frameworks` with a `#![test_runner]` —
//!   `main` calls the AUTHOR's runner.
//! * `test_case_default_runner`: `custom_test_frameworks` WITHOUT a runner — a
//!   user-written `#[test_case]` descriptor whose `testfn` is an arbitrary fn is
//!   run by a `main` whose MIR is byte-for-byte the builtin shape (MEASURED),
//!   so the shape check alone would have excluded it; the marker census refuses.
//!
//! Advisory policy keeps the verified bodies' findings nonfatal so the file pins
//! the disposition alone.
//!
//! MEASURED on the Track B stage 1 (2026-09-28): passes as annotated.

#![cfg_attr(marker, feature(rustc_attrs, test))]
#![cfg_attr(test_case_runner, feature(custom_test_frameworks))]
#![cfg_attr(test_case_runner, test_runner(crate::runner))]
#![cfg_attr(test_case_default_runner, feature(custom_test_frameworks, test))]

#[cfg(any(marker, test_case_default_runner))]
extern crate test;

#[cfg(marker)]
#[rustc_test_marker = "evil"]
pub const EVIL: test::TestDescAndFn = test::TestDescAndFn {
    desc: test::TestDesc {
        name: test::StaticTestName("evil"),
        ignore: false,
        ignore_message: None,
        source_file: "test_harness_exclusion_not_spoofable.rs",
        start_line: 1,
        start_col: 1,
        end_line: 1,
        end_col: 1,
        compile_fail: false,
        no_run: false,
        should_panic: test::ShouldPanic::No,
        test_type: test::TestType::UnitTest,
    },
    testfn: test::StaticTestFn(|| {
        let v = 5u32;
        let r = &v;
        let p = r as *const u32 as *const u8;
        let x: u8 = core::hint::black_box(200);
        let _y = x + 100;
        if p.is_null() { Err("null".to_string()) } else { Ok(()) }
    }),
};

#[cfg(test_case_runner)]
pub fn runner(tests: &[&fn() -> bool]) {
    for t in tests {
        let _ = t();
    }
}

#[cfg(test_case_runner)]
#[test_case]
pub const CASTS: fn() -> bool = || {
    let v = 5u32;
    let r = &v;
    let p = r as *const u32 as *const u8;
    !p.is_null()
};

#[cfg(test_case_default_runner)]
pub fn user_case() -> Result<(), String> {
    Ok(())
}

#[cfg(test_case_default_runner)]
#[test_case]
pub const T: test::TestDescAndFn = test::TestDescAndFn {
    desc: test::TestDesc {
        name: test::StaticTestName("t"),
        ignore: false,
        ignore_message: None,
        source_file: "test_harness_exclusion_not_spoofable.rs",
        start_line: 1,
        start_col: 1,
        end_line: 1,
        end_col: 1,
        compile_fail: false,
        no_run: false,
        should_panic: test::ShouldPanic::No,
        test_type: test::TestType::UnitTest,
    },
    testfn: test::StaticTestFn(user_case),
};
