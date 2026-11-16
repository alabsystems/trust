//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Cpanic=abort --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! FRESH-CAPTURE-1 negative controls (2026-10-18): the closure body of
//! `fresh_closure_capture_keeps_its_pointee.rs`, where the compiler can NOT account for
//! every value of the closure type, keeps CALL-HAVOC-ESCAPE-2's havoc of the captured
//! pointee at the call, so the remainder after the call stays refuted (the division
//! before it is guarded and proves):
//!
//! * `passed_to_generic`: the closure VALUE reaches generic code, which could
//!   `transmute_copy` a value of its type whose capture carries raw-pointer bits;
//! * `copied`: a second local of the closure type (a copy) is called too;
//! * `returned`: the closure leaves its parent (`impl Fn`), so callers hold its type;
//! * `generic_parent`: the parent is generic (no premise is minted under a generic
//!   parent, exactly as for `ADAPTER_YIELD`).

#[inline(never)]
pub fn opaque_sink(x: usize) -> usize {
    core::hint::black_box(x)
}

#[inline(never)]
fn apply<F: Fn(usize) -> usize>(f: F, p: usize) -> usize {
    f(p)
}

pub fn passed_to_generic(w: usize, p: usize) -> usize {
    apply(
        |p: usize| {
            //~^ NOTE [remzero] FAILED
            if w == 0 {
                return 0;
            }
            let q = p / w;
            opaque_sink(q);
            p % w
        },
        p,
    )
}

pub fn copied(w: usize, p: usize) -> usize {
    let f = |p: usize| {
        //~^ NOTE [remzero] FAILED
        if w == 0 {
            return 0;
        }
        let q = p / w;
        opaque_sink(q);
        p % w
    };
    let g = f;
    f(p) ^ g(p)
}

pub fn returned(w: &usize) -> impl Fn(usize) -> usize + '_ {
    |p: usize| {
        //~^ NOTE [remzero] FAILED
        if *w == 0 {
            return 0;
        }
        let q = p / *w;
        opaque_sink(q);
        p % *w
    }
}

pub fn generic_parent<T>(w: usize, p: usize, _t: T) -> usize {
    let f = |p: usize| {
        //~^ NOTE [remzero] FAILED
        if w == 0 {
            return 0;
        }
        let q = p / w;
        opaque_sink(q);
        p % w
    };
    f(p)
}
