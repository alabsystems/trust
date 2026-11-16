//@ needs-trust-verify
//@ aux-build: spoof_std_print_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! HOLE A pin (2026-09-14). The default policy tolerates the std stdout/stderr
//! print backend absent-callee row as a foundational-TCB completeness gap. That
//! grace used to be keyed on `.contains("std::io::_print")` over the callee's
//! RENDERED def path, which is SPOOFABLE: a verify-off dependency defining
//! `a::std::io::_print` (via user modules named `std`/`io`) renders a path that
//! CONTAINS `std::io::_print`, so its `panic!()` was classified as std's benign
//! broken-pipe backend and TOLERATED — compile exit 0 while the program panics
//! at runtime (a false SAFE claim).
//!
//! The fix classifies the print backend by the callee's REAL crate (`CrateNum`
//! == the std sysroot crate) plus EXACT def-path segments, never a substring —
//! see `def_is_std_print_backend` / `def_path_str_is_std_print_backend` /
//! `callee_is_masked_fail_closed_dispatch` in
//! `compiler/rustc_mir_transform/src/trust_verify.rs`. The spoof's crate root is
//! `spoof_std_print_dep`, not `std`, so it becomes an ordinary absent callee and
//! MUST stay fatal. This file MUST stay red.
extern crate spoof_std_print_dep;

pub fn call_spoof(v: i32) -> i32 {
    // A verified function calling the spoofed print backend. Its panic-freedom is
    // an unproven absent-callee obligation that must NOT be laundered as the
    // tolerated std print gap.
    spoof_std_print_dep::a::std::io::_print(v)
}
