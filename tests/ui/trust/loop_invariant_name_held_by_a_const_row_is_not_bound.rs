//@ revisions: inner_shadow inner_shadow_debuginfo param_copy_debuginfo dropped_last_name_debuginfo
//@ revisions: const_item static_item stripped_rows merged_by_dest_prop
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[inner_shadow_debuginfo] compile-flags: -Cdebuginfo=2
//@[param_copy_debuginfo] compile-flags: -Cdebuginfo=2
//@[dropped_last_name_debuginfo] compile-flags: -Cdebuginfo=2
//@[stripped_rows] compile-flags: -Zmir-strip-debuginfo=all-locals
//@[merged_by_dest_prop] compile-flags: -Zmir-opt-level=2 -Cdebuginfo=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The debug-name census counted only rows naming a whole plain local. When the
//! binding in scope at a loop is folded to `debug lim => const 200_u8`, another
//! `lim` (an inner-block shadow, or the parameter a copy-propagated shadow sits
//! on) held the name alone, and the loop invariant was PROVED about that local
//! while the `lim` in scope breaks it (review round 38, 2026-10-02; `f(1)` and
//! `f(50)` violate the invariant at the loop head). `dropped_last_name`: once a
//! local's last name was dropped as shared, an earlier `x` row on it won while
//! the `x` in scope is the constant 7. Every row now counts as a holder.
//! Review round 39: a block-local `const`/`static lim` shadows an outer `let lim`
//! but is no pattern binding (`const_item`, `static_item`); StripDebugInfo removed
//! the in-scope shadow's row, leaving only the shadowed parameter's
//! (`stripped_rows`); DestinationPropagation merged `lim` into a later-mutated `k`
//! (`merged_by_dest_prop`). Each was PROVED and kernel-certified.
#[cfg(any(inner_shadow, inner_shadow_debuginfo))]
#[allow(unused_variables)]
pub fn f(a: u8) -> u8 { //[inner_shadow,inner_shadow_debuginfo]~ ERROR verification
    let lim: u8 = 200;
    {
        let lim: u8 = a / 4;
    }
    let mut k: u8 = 0;
    while k < a
        invariant lim <= 100
    {
        k += 1;
    }
    k
}

#[cfg(param_copy_debuginfo)]
#[allow(unused_variables)]
pub fn f(a: u8) -> u8 { //[param_copy_debuginfo]~ ERROR verification
    let lim: u8 = 10;
    {
        let lim: u8 = a;
    }
    let mut k: u8 = 0;
    while k < a
        invariant k <= lim
    {
        k += 1;
    }
    k
}

#[cfg(dropped_last_name_debuginfo)]
#[allow(unused_variables)]
pub fn f(a: u8) -> u8 { //[dropped_last_name_debuginfo]~ ERROR verification
    let s = a ^ a;
    let x = s;
    let n = x;
    let n = a & n;
    let x = 7u8;
    let mut i = 0u8;
    while i < 3
        invariant x == 0
    {
        i += 1;
    }
    s + i + n
}

#[cfg(any(const_item, static_item))]
#[allow(non_upper_case_globals, unused_variables)]
pub fn f(a: u8) -> u8 {
    let lim: u8 = a / 2;
    let mut i: u8 = 0;
    {
        #[cfg(const_item)]
        const lim: u8 = 200;
        #[cfg(static_item)]
        static lim: u8 = 200;
        while i < 3
            invariant lim <= 127
        {
            i += 1;
        }
    }
    i + lim
}

#[cfg(stripped_rows)]
#[allow(unused_variables)]
// Re-pinned 2026-10-15: since a39074ae82f (determinism T6, 2026-10-09) a proof session refuses
// `-Zmir-strip-debuginfo` outright, before any verification runs: the verified MIR, and so the verdict, must
// not depend on the caller's MIR options. The shape this revision built can no longer reach
// a verdict at all, which is the strongest form of the refusal it pinned.
//[stripped_rows]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-strip-debuginfo would make the verified MIR
pub fn f(lim: u8) -> u16 {
    let lim: u16 = 300;
    let mut i: u16 = 0;
    while i < 3
        invariant lim <= 255
    {
        i += 1;
    }
    i
}

#[cfg(merged_by_dest_prop)]
#[allow(unused_variables, unused_assignments)]
// Re-pinned 2026-10-15: since a39074ae82f (determinism T6, 2026-10-09) a proof session refuses
// `-Zmir-opt-level` outright, before any verification runs: the verified MIR, and so the verdict, must
// not depend on the caller's MIR options. The shape this revision built can no longer reach
// a verdict at all, which is the strongest form of the refusal it pinned.
//[merged_by_dest_prop]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-opt-level would make the verified MIR
pub fn f(a: u8) -> u8 {
    let mut k: u8;
    let lim: u8 = a / 2;
    k = lim;
    k |= 128;
    let mut i: u8 = 0;
    while i < 3
        invariant lim >= 128
    {
        i += 1;
    }
    k + (i - i)
}
