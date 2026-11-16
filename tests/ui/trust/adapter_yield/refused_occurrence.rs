//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: Trust modeled fact
//! D2 tier 1 (2026-09-24): the OCCURRENCE discipline. `ADAPTER_YIELD` holds
//! only if core's adapter is the one and only thing that can invoke the
//! closure's body, so every mention of the closure's type in its parent must be
//! the single by-value adapter argument (or, for `filter`/`map`, the lazy
//! adapter moved once into a core consumer). Each closure below is reachable
//! some other way, and each must stay refused, with the premise NEVER installed
//! (`forbid-output`), in BOTH revisions:
//!
//! * `direct_call` — called directly on `&[]` (PANICS) as well as by `all`.
//! * `reused` — handed to two adapters; the second is `chunks(1)` (PANICS).
//! * `by_mut_ref` — `all(&mut c)` (`F == &mut C`), then called on `&[]` (PANICS).
//! * `fn_pointer` — coerced to `fn(&[u32]) -> bool`, called on `&[]` (PANICS).
//! * `escapes` — the `Filter` carrying the predicate is RETURNED
//!   (conservative non-admission: this program is safe).
//! * `nested` — the closure's parent is another closure (conservative).
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): every closure is
//! refused with `[slice] FAILED` on its own root, exactly as pinned here.

pub fn direct_call(v: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    //~^ NOTE [slice] FAILED
    c(&[]) || v.windows(2).all(c)
}

pub fn reused(v: &[u32], u: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    //~^ NOTE [slice] FAILED
    v.windows(2).all(c) && u.chunks(1).all(c)
}

pub fn by_mut_ref(v: &[u32]) -> bool {
    let mut c = |w: &[u32]| w[0] <= w[1];
    //~^ NOTE [slice] FAILED
    let r = v.windows(2).all(&mut c);
    r && c(&[])
}

pub fn fn_pointer(v: &[u32]) -> bool {
    let c = |w: &[u32]| w[0] <= w[1];
    //~^ NOTE [slice] FAILED
    let p: fn(&[u32]) -> bool = c;
    p(&[]) || v.windows(2).all(c)
}

pub fn escapes(v: &[u32]) -> impl Iterator<Item = &[u32]> {
    v.windows(2).filter(|w| w[0] <= w[1])
    //~^ NOTE [slice] FAILED
}

pub fn nested(vs: &[&[u32]]) -> bool {
    vs.iter().all(|v| v.windows(2).all(|w| w[0] <= w[1]))
    //~^ NOTE [slice] FAILED
}
