//@ revisions: interval native calls opaque tailcall sentinel control
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type lib
//@ rustc-env: TRUST_VERIFY_ROW_DIAGNOSTICS=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
// Each complete diagnostic line contains ONE canonical public row. Match the
// aggregate's own outcome and final grade, never a sibling's certificate. The
// optional location is the canonical flat SourceSpan; premises contain only
// enum strings, so the final grade cannot swallow another nested grade.
//@[interval] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::interval_only_sibling","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__interval_only_sibling:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":(?:"runtime_checked",[^\n]*|"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"(?:compiler-composed|solver-asserted|solver-self-checked)","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\})\}\}$
//@[native] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::native_only_sibling","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__native_only_sibling:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":(?:"runtime_checked",[^\n]*|"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"(?:compiler-composed|solver-asserted|solver-self-checked)","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\})\}\}$
//@[calls] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::registry_discharged_call","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__registry_discharged_call:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":(?:"runtime_checked",[^\n]*|"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"(?:compiler-composed|solver-asserted|solver-self-checked)","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\})\}\}$
//@[opaque] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::guard_behind_a_call","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__guard_behind_a_call:assertion:panic-freedom:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":(?:"runtime_checked",[^\n]*|"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"(?:compiler-composed|solver-asserted|solver-self-checked)","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\})\}\}$
//@[tailcall] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::tail_after_dead_panic","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__tail_after_dead_panic:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":(?:"runtime_checked",[^\n]*|"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"(?:compiler-composed|solver-asserted|solver-self-checked)","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\})\}\}$
// Six bodies also have a separately certified, unreachable outlined panic site.
//@[interval] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::interval_only_sibling","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[native] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::native_only_sibling","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[calls] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::registry_discharged_call","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[opaque] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::guard_behind_a_call","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[tailcall] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::tail_after_dead_panic","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[control] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::certified_sibling","row":\{[^\n]*"description":"assertion: panic call: core::panicking::panic_default_msg"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[sentinel] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::sited_sentinel","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__sited_sentinel:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//@[control] regex-error-pattern: (?m)^TRUST_ROW_DIAGNOSTIC:\{"function":"grounded_catchall_inherits_weakest_premise::certified_sibling","row":\{"obligation_id":"vc:grounded_catchall_inherits_weakest_premise__certified_sibling:assert:0",[^\n]*"description":"assertion: panic freedom: [^"]*"(?:,"location":\{"file":"[^"]*","line_start":\d+,"col_start":\d+,"line_end":\d+,"col_end":\d+\})?,"outcome":"proved",[^\n]*,"grade":\{"encoding":"unvalidated-encoder","discharge":"kernel-reference-checked","premises":\[(?:"[a-z-]+"(?:,"[a-z-]+")*)?\]\}\}\}$
//! A GROUNDED whole-function panic-freedom catch-all may not report a grade
//! above the weakest premise it stands on (NEW-CATCHALL, 2026-09-24).
//!
//! Two rewrites re-point the catch-all (`panic freedom: no assertion, …`) at
//! a formula the Clean kernel can re-check, and `certify_all` then certifies
//! that formula. The certificate is genuine; what it does not check is what
//! the rewrite assumed:
//!
//! * `refute_full_assert_obligations` proves each `assert!`/`panic!` block
//!   unreachable and re-points the catch-all at the OR of their feasibility
//!   formulas — after reading every OTHER row's `Proved` LABEL (before any
//!   proof authority exists) and after its call gate discharged every other
//!   `Terminator::Call` from a registry. The gate enumerates calls only: a
//!   tail call is never examined at all;
//! * `ground_panic_freedom_catchall` re-points an already-`Proved` opaque
//!   catch-all at the OR of its SIBLINGS' formulas — which says nothing about
//!   a panic source that has no sibling row, and the aggregate exists exactly
//!   for such sources.
//!
//! Every body below has one arithmetic, call or tail-call site and one
//! `panic!()` or `unreachable!()` that no input reaches. MEASURED on the
//! unfixed stage1 (compiletest's flags, edition 2021, `-Ztrust-verify-output=json`
//! for the row attribution), at `d485fe0ff7`, `7ef9f15c0a` and `521477a0d2`:
//!
//! * `interval` — `(a | 0x80) - 0x80`: at `7ef9f15c0a` and `521477a0d2` the
//!   interval lane closed the subtraction with no authority at all (wire:
//!   `runtime_checked`, solver `interval`, "solver reported Proved without
//!   exact kernel/native proof authority" — `DECISION_QUEUE.md` D3) and the
//!   catch-all reported `clean-kernel/Certified` beside it; at `d485fe0ff7`
//!   the native lane closed it instead (`trust-mc`/`Pdr`, `Trusted`) and the
//!   catch-all was still `Certified`.
//! * `native` — `a / (b | 1)`: the divisor row ended `trust-mc`/`Pdr`
//!   (`Trusted`), the catch-all `Certified` over it.
//! * `calls` — the call to `half` was discharged by the call gate from the
//!   panic-free registry; the catch-all, whose only sibling set was empty,
//!   reported `Certified` although nothing the kernel saw covers `half`.
//! * `opaque` — `five()` hides the guard from the refute lane (its formula is
//!   ungrounded) and the call gate refuses the bare `core::panicking::panic`,
//!   so only the native CHC/PDR lane proved the opaque catch-all. The sibling
//!   rewrite then re-pointed it at the overflow row's formula ALONE and it
//!   reported "of which 2 kernel-certified" — a certificate about `+ 1`
//!   standing for a claim about `panic!()`.
//! * `tailcall` — `become scramble(x, n)` beside a dead `panic!()`: the refute
//!   lane's gate reported every call discharged without ever looking at the
//!   tail call, and the catch-all reported `Certified`. (`scramble` happens to
//!   be panic-free; nothing established that for this row.)
//!
//! After the fix the catch-all of `interval`, `native`, `calls` and `tailcall`
//! is not kernel-certified: it reports `Trusted`
//! (`GroundedPanicFreedomDerivation`) over a `Trusted` premise or a
//! registry-discharged call, and keeps no authority over an unproved premise
//! or an unexamined tail call. In `opaque` the sibling rewrite declines and the
//! catch-all keeps its native `trust-mc` CHC/PDR proof (`Trusted`), leaving the
//! aggregate without kernel credit. Outlined `panic_default_msg` handling now
//! also proves the independently unreachable panic site with its own genuine
//! kernel certificate. That additional row cannot grant aggregate authority.
//! Which lane closes a sibling can
//! depend on machine load (the native lane runs under a wall-clock budget), so
//! the checks pin only what holds in every outcome.
//!
//! `sentinel` and `control` keep the kernel grade where it is earned, so the
//! exact row checks above cannot pass by suppressing the note: `sentinel` is the
//! sibling rewrite over an `unreachable!()` whose own per-site row covers the
//! only panic source, `control` is the refute rewrite over a sibling the kernel
//! certifies itself (`(a & 0x7f) + 1`) with no call beyond the panic.

// `become` is feature-gated when it is PARSED, before `cfg` strips the
// `tailcall` item, so the gate is on for every revision; it admits syntax only.
#![feature(explicit_tail_calls)]

#[cfg(interval)]
pub fn interval_only_sibling(a: u8, n: u32) -> u8 {
    //[interval]~^ NOTE Trust verification:
    let r = (a | 0x80) - 0x80;
    if n == 7 && n == 8 {
        panic!();
    }
    r
}

#[cfg(native)]
pub fn native_only_sibling(a: u32, b: u32, n: u32) -> u32 {
    //[native]~^ NOTE Trust verification:
    let q = a / (b | 1);
    if n == 7 && n == 8 {
        panic!();
    }
    q
}

#[cfg(calls)]
fn half(x: u8) -> u8 {
    x / 2
}

#[cfg(calls)]
pub fn registry_discharged_call(x: u8) -> u8 {
    //[calls]~^ NOTE Trust verification:
    if x > 5 && x < 3 {
        panic!();
    }
    half(x)
}

#[cfg(opaque)]
fn five() -> u32 {
    5
}

#[cfg(opaque)]
pub fn guard_behind_a_call(n: u8) -> u8 {
    //[opaque]~^ NOTE Trust verification:
    //[opaque]~| NOTE of which 2 kernel-certified by the clean CIC kernel
    let k = five();
    if k != 5 {
        panic!();
    }
    (n & 0x7f) + 1
}

#[cfg(tailcall)]
fn scramble(x: u32, n: u32) -> u32 {
    (x / 2) ^ (n / 3)
}

#[cfg(tailcall)]
pub fn tail_after_dead_panic(x: u32, n: u32) -> u32 {
    //[tailcall]~^ NOTE Trust verification:
    if n == 7 && n == 8 {
        panic!();
    }
    become scramble(x, n)
}

#[cfg(sentinel)]
pub fn sited_sentinel(n: u32) -> u32 {
    //[sentinel]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[sentinel]~| NOTE of which 2 kernel-certified by the clean CIC kernel
    let k = n % 4;
    if k >= 4 {
        unreachable!()
    }
    k
}

#[cfg(control)]
pub fn certified_sibling(a: u8, n: u32) -> u8 {
    //[control]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[control]~| NOTE of which 3 kernel-certified by the clean CIC kernel
    let b = (a & 0x7f) + 1;
    if n == 7 && n == 8 {
        panic!();
    }
    b
}
