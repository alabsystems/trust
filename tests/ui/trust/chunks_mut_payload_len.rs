//@ revisions: default certify advisory reseat
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[default] check-pass
//@[certify] check-pass
//@[advisory] check-pass
//@[reseat] check-fail
//@[advisory] forbid-output: [bounds] FAILED
//@[advisory] forbid-output: [slice] FAILED
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[reseat] dont-require-annotations: ERROR
//! The payload of `chunks_exact_mut`/`chunks_mut`/`rchunks*_mut` carries its chunk length
//! (CHUNKS-MUT-PAYLOAD-1; KNOWN_HAZARDS, 2026-10-11).
//!
//! `trust_vcgen::container_len::build_slice_iter_yield_guard_map` mints `len(w) == n`
//! (`chunks_exact*`) or `1 <= len(w) <= n` (`chunks*`) on the `Some` payload `w` of a
//! `next` on such an iterator. It gated that fact on
//! `iterator_yield::payload_carries_global_fact`, plain `is_single_static_assignment(w)`.
//! An index through a `&mut [T]` makes rustc read the length through its own
//! `&raw const (*w)`, and `Statement::escapes_local` counts that Deref-first borrow as an
//! escape of `w`, so the `_mut` payload got no fact and `w[3]` was refuted at
//! `w__slice_len = 0`, a length these iterators never yield. The read-only twin
//! (`chunks_exact`) has no raw borrow and proved. The gate is now the `{s}__slice_len`
//! name licence (`slice_len_licence::licensed_slice_len_formula`, the one that already
//! licenses a guarded `&mut [u8]` parameter's length): a borrow of `*w` or an element
//! store cannot change the fat pointer's metadata, while a reseat of `w` and a mutable
//! borrow of `w` itself are still refused (the `reseat` revision).
//!
//! BEFORE (the wave-25 probe stage 1, `scratchpad/stage1-w25probe`, which carries wave
//! 24, measured 2026-10-12 with this header's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no --emit=metadata --error-format=json -A unused`):
//! `default` and `certify` exit 1 with 8 errors: each of `chex_mut`, `chex_mut_read`,
//! `whilelet_mut` and `len_and_index` is refused on a `bounds`, `slice` or `overflow:sub`
//! row that FAILED with `w__slice_len#… = 0` in its counterexample; `advisory` exits 0
//! but publishes six such failed rows (the four, plus a `bounds` row of each of
//! `chunks_mut_first` and `rchex_mut`); `reseat` exits 1 with 4 errors, both functions
//! refused on a failed `bounds` row.
//!
//! AFTER (measured 2026-10-13 on the integ/wave25 stage 1): `default`, `certify` and
//! `advisory` exit 0 with no FAILED row; `reseat` still exits 1 with both functions
//! refused. vcgen's half is pinned on real MIR in
//! `crates/trust-vcgen/tests/slice_iter_yield_bounds.rs`.
//!
//! `chunks_mut_first` and `rchex_mut` keep a separate trust-mc `assertion:panic-freedom`
//! `runtime_checked` row ("Alloca without an internally bound extent"). The default
//! policy (`strict`) reports that row as a warning and does not fail it; `certify` and
//! `memory-safe` refuse it. So the two are in `default` (check-pass: their bounds rows
//! were the only refusal, measured 2026-10-13: BEFORE they add `[bounds] FAILED` errors,
//! AFTER they compile with the runtime-checked warning) and `advisory` (the pin that no
//! bounds row is FAILED), and not in `certify`.

#[cfg(any(default, certify, advisory))]
pub fn chex_mut(a: &mut [u8]) {
    for w in a.chunks_exact_mut(4) {
        w[3] = 1;
    }
}

#[cfg(any(default, certify, advisory))]
pub fn chex_mut_read(a: &mut [u8]) -> u8 {
    let mut s = 0u8;
    for w in a.chunks_exact_mut(4) {
        s ^= w[3];
    }
    s
}

#[cfg(any(default, certify, advisory))]
pub fn len_and_index(a: &mut [u8]) -> usize {
    let mut s = 0;
    for w in a.chunks_exact_mut(4) {
        s ^= w.len() - 4;
        w[0] = 1;
    }
    s
}

#[cfg(any(default, certify, advisory))]
pub fn whilelet_mut(a: &mut [u8]) {
    let mut it = a.chunks_exact_mut(4);
    while let Some(w) = it.next() {
        w[3] = 1;
    }
}

#[cfg(any(default, advisory))]
pub fn chunks_mut_first(a: &mut [u8]) {
    for w in a.chunks_mut(4) {
        w[0] = 1;
    }
}

#[cfg(any(default, advisory))]
pub fn rchex_mut(a: &mut [u8]) {
    for w in a.rchunks_exact_mut(2) {
        w[1] = 7;
    }
}

// ---- reseat: `w` names another slice by the time it is indexed; each panics for a
// short `other` and must stay refused ----

#[cfg(reseat)]
pub fn reseat(a: &mut [u8], other: &mut [u8]) {
    //[reseat]~^ ERROR Trust Level 0 safety verification incomplete for `chunks_mut_payload_len::reseat`
    for mut w in a.chunks_exact_mut(4) {
        w = &mut other[..];
        w[3] = 1;
    }
}

#[cfg(reseat)]
pub fn reseat_via_ref(a: &mut [u8], other: &mut [u8]) {
    //[reseat]~^ ERROR Trust Level 0 safety verification incomplete for `chunks_mut_payload_len::reseat_via_ref`
    for mut w in a.chunks_exact_mut(4) {
        let p = &mut w;
        *p = &mut other[..];
        w[3] = 1;
    }
}
