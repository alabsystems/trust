//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:inlined_panic_dep.rs
//@ aux-build:inlined_panic_dep_backstop.rs
//@ revisions: unwrap_o0
//@ revisions: dep_abort_o0 dep_force_inline_default
//@ revisions: from_str_radix_o0 push_o0
//@ revisions: from_str_radix_o0_abort
//@ revisions: from_digit_o0 from_digit_o0_abort
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[from_str_radix_o0_abort] compile-flags: -Cpanic=abort
//@[from_digit_o0_abort] compile-flags: -Cpanic=abort
//@[unwrap_o0] check-fail
//@[dep_abort_o0] check-fail
//@[dep_force_inline_default] check-fail
//@[from_str_radix_o0] check-fail
//@[push_o0] check-pass
//@[from_str_radix_o0_abort] check-fail
//@[from_digit_o0] check-fail
//@[from_digit_o0_abort] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (2026-09-29): A PANIC PATH THE MIR INLINER COPIED IN FROM FOREIGN CODE
//! IS NEVER A RUNTIME CHECK THE USER WROTE
//! (`compiler/rustc_mir_transform/src/trust_verify/inlined_sysroot_panic.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-29 — under an explicit
//! `-Zinline-mir=yes` (or `-Zmir-opt-level=2`), an inlined std panic is a
//! tolerated runtime-checked row").
//!
//! A verifying session compiles every `-Copt-level` from the `-O0` MIR pipeline,
//! where a panicking std call is a `Call` its call-site row refuses and a
//! dependency's call is fail-closed. An EXPLICIT `-Zinline-mir=yes` or
//! `-Zmir-opt-level>=2` is honored: the callee is inlined, its panic path
//! (`option::unwrap_failed`, `option::expect_failed`,
//! `core::str::slice_error_fail`, a dependency's `std::process::abort()`, ...)
//! lands in the caller inside an `(inlined <callee>)` scope, the whole-function
//! panic-freedom row keeps its `Assertion` runtime fallback (or reaches a
//! tolerated vanilla sysroot callee), and the default policy tolerated it.
//!
//! Every check-fail revision except the two `_o0` controls built rc=0 on main
//! (`0.10.0+g4715fe060`, source of `7eddcd160b`), and its program, driven by a
//! `-Ztrust-verify=off` binary through the same rlib, panicked (exit 101) or
//! aborted: `f(None)`, `f(Some(None))`, `g("é")`, `h("ab", 9)`, `i("é", 1)`,
//! `d[4]` on a one-element deque (probes `a_unwrap`, `a_somenone`, `a_split`,
//! `a_splitk`, `a_strslice`, `q24_deque_mir3_index` in
//! `salvage-2026-09-28/work/fix-trust-open-false-accepts/repro`, and the OFA-r1
//! round), and the dependency's `ab(7)` / `gt(&[], 0)`. `unwrap_o0` and
//! `dep_abort_o0` are the `-O0` controls: refused before and after, by the
//! call-site row and the dependency call's fail-closed row.
//! `dep_force_inline_default` needs NO flag: the dependency's `fab` is
//! `#[rustc_force_inline]`, which the ForceInline pass inlines at every
//! mir-opt-level, so its `abort()` rode the tolerance at the verifying default
//! (rc=0 on main).
//!
//! Each inlined refusal names the site (`NOTE a panic path inlined from`).
//! `str_prefix_inl` also keeps a runtime-checked bundled std member (`get`), so
//! it is refused by that disposition's gate (`runtime_checked_std_member_withheld`)
//! before the tolerance is reached; the note is the same.
//!
//! The check-pass revisions are the controls that the rule refuses only a
//! foreign panic path: an inlined std method with NO panic path (`unwrap_or`,
//! `split_at_checked`) and a user `if let`, built under `-Zinline-mir=yes`.
//!
//! A PANIC PATH THROUGH A CALL THE INLINER LEFT (resume 2026-09-30, OFA-r3
//! prescan). `u32::from_str_radix(s, radix)` panics when `radix` is outside
//! `2..=36`; at `-O0` its call-site row refuses it (`from_str_radix_o0`). Under
//! `-Zinline-mir=yes` (and a hint threshold of 5) `from_str_radix` is inlined to a
//! RETURNING call of `from_ascii_radix`, where the panic lives: no `Assert`, no
//! diverging call in the inlined scope, so the first rule (dev2) found no site,
//! and the build was rc=0 on main `0.10.0+g4715fe060`. A call that can unwind to
//! a callee this crate does not define, inside a foreign inlined scope, is a
//! panic site too (`from_str_radix_inl`, `from_str_radix_t5`). `str_range_t15` is
//! the second shape the prescan found: under a threshold of 15, `s[a..b]` inlines
//! `<ops::Range<usize> as SliceIndex<str>>::index` to a returning call of the
//! `range::Range<usize>` impl, which no `-O0` lane names. The disclosed cost
//! of that widening is `push_inl`: `Vec::push` inlines to a `push_mut` call, so
//! the growth row the `-O0` pipeline tolerates (`push_o0`, check-pass) must now
//! prove under the explicit flag, and does not.
//!
//! AN ABORTING PANIC STRATEGY (2026-09-30, adversarial round against the widened
//! rule). Under `-Cpanic=abort` the MIR pipeline gives every Rust call an
//! `unwind unreachable` edge, so the returning-call rule, which read that edge as
//! "the callee cannot panic", skipped the very calls it was widened for:
//! `from_str_radix_inl_abort` inlines to
//! `from_ascii_radix(..) -> [return: bb1, unwind unreachable]` and
//! `str_range_t15_abort` to `<range::Range<usize> as SliceIndex<str>>::index(..)
//! -> [return: bb1, unwind unreachable]`. Both built rc=0 on main
//! `0.10.0+g07091c92c`, each refused at `-O0` with the same `-Cpanic=abort`
//! (`from_str_radix_o0_abort`, the control). Under a strategy that does not
//! unwind, the unwind edge of a returning foreign call says nothing, so the
//! callee's own declaration is asked: the call is a site unless the callee is
//! nounwind by declaration (`#[rustc_nounwind]`, the flag behind the same call's
//! `unwind unreachable` edge in a session that unwinds).
//! `unwrap_or_inl_abort` is the control that the abort arm refuses only a
//! foreign panic path (rc=0 on main, and still check-pass).
//! `local_helper_inl_abort` (2026-10-08) is the control for that declaration
//! test: `local_helper_inl`'s source under `-Zinline-mir=yes -Cpanic=abort`.
//! `count_ones` inlines to a call of the intrinsic `ctpop`, which panics in no
//! session; the rule's second version (every returning foreign call is a site
//! under an aborting strategy) refused the helper on "a call to `ctpop` that can
//! panic" (rc=1 on the branch at `0.10.0+g7a237b737`; rc=0 there under either
//! flag alone, and rc=0 on main).
//!
//! THE PIN ON THE MAIN THIS LANDS ON (2026-10-08, main `0.10.0+gde6288ddd`). Main
//! moved under the fixture: its own verifier now refuses `from_str_radix_inl`,
//! `_t5`, `_inl_abort`, `str_range_t15` and `_abort` by itself (the returning
//! callee's body is now in the function's bundle and its panic is a refuted
//! assertion row), so of the revisions above only `push_inl`, the disclosed
//! cost, still builds rc=0 there. The class is not closed on main:
//! `char::from_digit(d, radix).unwrap_or('x')` panics when `radix > 36`, is
//! refused at `-O0` (`from_digit_o0`, `from_digit_o0_abort`), and under
//! `-Zinline-mir=yes` or `-Zmir-opt-level=3 -Copt-level=3` inlines to a
//! RETURNING call of `core::char::convert::from_digit`, where the panic lives.
//! Measured on main `de6288dddf`: `from_digit_inl` and `from_digit_mir3` build
//! rc=0 ("1 proved ... 1 runtime-checked") and `u(1, 40)`, driven verify-off
//! through that rlib, exits 101 ("from_digit: radix is too high (maximum 36)");
//! `from_digit_inl_abort` builds rc=0 and aborts (134). They are the VERDICT
//! pins of the returning-call arm, the gap gate and the aborting-strategy
//! handling on this main (`convert::from_digit` is not nounwind by
//! declaration, so the declaration test above does not excuse it).
//!
//! WHAT EACH ARM'S PIN IS (2026-10-04, the landing review's planted defects,
//! `work/review-trust-open-false-accepts/fx-*.log`, and
//! `work/fix-trust-open-false-accepts/land-r1/probe`).
//! * The returning-call arm, the gap gate and the aborting-strategy handling are
//!   pinned by VERDICT: disabling one turns `from_str_radix_inl`/`_t5`/
//!   `_inl_abort`, `push_inl`, `str_range_t15`/`_abort` into exit-0 builds
//!   (on the mains of 2026-10-04; on main `de6288dddf`, `push_inl` and the
//!   `from_digit_*` revisions of the section above).
//! * The `Assert`/diverging-call arm, the dependency owner and the std-member
//!   disposition are pinned by the NOTE only (disabling one fails the
//!   `NOTE a panic path inlined from` and `str_prefix_inl`'s full-verification
//!   annotations): every shape they read is also refused by main's
//!   `[inlined-panic-path]` row (an `Assert` or diverging call under an outermost
//!   non-local scope), or, under an outermost LOCAL scope, by the local callee's
//!   own verification, which charges the same inlined std panic in its own body
//!   (measured: a local `#[inline] fn helper(o) { o.unwrap() }` and its generic
//!   and closure twins are refused in the helper on main `9fc182f094` and here,
//!   and here also in the caller). A crate verdict cannot pin them.
//! * The LOCAL-scope exemption is pinned by `local_helper_inl` (check-pass): a
//!   local `#[inline]` helper whose user `assert!` stays a tolerated
//!   runtime-checked row is inlined into its caller; treating that local scope as
//!   foreign refuses the caller (measured with the review's `a_local` mutant).
//! * The tail-call arm cannot be reached: the MIR inliner never inlines a body
//!   with a tail call (`compiler/rustc_mir_transform/src/inline.rs`, "can't
//!   inline functions with tail calls"), and `#[rustc_force_inline]` on one is a
//!   compile error ("`ftl` is incompatible with `#[rustc_force_inline]`"), so no
//!   `TailCall` terminator sits under an inlined scope. `dep_tail_inl` pins the
//!   shape: the dependency's `#[inline]` tail-calling `tl` stays a call and is
//!   refused as a call into a verify-off crate. The arm stays as a backstop
//!   should the inliner learn to inline tail calls.
//! * The inline-assembly arm is a backstop too: a dependency's `noreturn` asm
//!   IS inlined under `-Zinline-mir=yes`, and the body is refused first, by the
//!   native lowering gate ("native typed-TrustIr lowering did not complete, so
//!   the panic-freedom of an unmodeled construct could not be established"),
//!   with or without the arm. `dep_asm_inl` pins that verdict.

#[cfg(any(dep_abort_o0, dep_force_inline_default))]
extern crate inlined_panic_dep;

#[cfg(unwrap_o0)]
pub fn f(o: Option<u8>) -> u8 {
    //[unwrap_o0]~^ ERROR Trust strict verification failed for `inlined_sysroot_panic_refused::f`
    o.unwrap()
}

#[cfg(dep_abort_o0)]
pub fn k(x: u32) -> u32 {
    //[dep_abort_o0]~^ ERROR Trust strict verification failed for `inlined_sysroot_panic_refused::k`
    inlined_panic_dep::ab(x)
}

#[cfg(dep_force_inline_default)]
pub fn k(x: u32) -> u32 {
    //[dep_force_inline_default]~^ ERROR Trust strict verification failed for `inlined_sysroot_panic_refused::k`
    //[dep_force_inline_default]~| NOTE a panic path inlined from
    inlined_panic_dep::fab(x)
}

#[cfg(any(from_str_radix_o0, from_str_radix_o0_abort))]
pub fn r(s: &str, radix: u32) -> u32 {
    //[from_str_radix_o0,from_str_radix_o0_abort]~^ ERROR Trust strict verification failed for `inlined_sysroot_panic_refused::r`
    u32::from_str_radix(s, radix).unwrap_or(0)
}

#[cfg(push_o0)]
pub fn p(v: &mut Vec<u32>, x: u32) {
    v.push(x)
}

#[cfg(any(from_digit_o0, from_digit_o0_abort))]
pub fn u(d: u32, radix: u32) -> char {
    //[from_digit_o0,from_digit_o0_abort]~^ ERROR Trust strict verification failed for `inlined_sysroot_panic_refused::u`
    char::from_digit(d, radix).unwrap_or('x')
}
