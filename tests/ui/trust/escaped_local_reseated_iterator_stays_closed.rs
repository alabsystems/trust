//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//~? RAW Trust
//! Trust: 2026-09-16 — THE ORIGIN LANE MUST NOT RE-OPEN THE ESCAPE HOLE.
//!
//! `escaped_local_for_loop_iterator_still_proves.rs` pins that the `for`-loop
//! tracers recovered their precision by asking the ORIGIN question
//! (`local_defs::unique_initializing_def`) about the loop's iterator local
//! instead of the value resolver that now refuses the `&mut` alias. That lane is
//! licensed by ONE gate, `generate::iterator_yield::iter_mut_borrows_only_feed_next`:
//! every `&mut`/`&raw` conduit of the local is defined once and used ONLY as the
//! receiver of a std `Iterator::next` call — never read, never WRITTEN THROUGH,
//! never dropped, never passed anywhere else.
//!
//! THIS file is the program that gate exists to refuse. `it` is a genuine
//! iterator whose conduit `p` is used only for a deref STORE, which reseats the
//! whole iterator onto `0..100` before the loop runs. MEASURED on the pristine
//! prebuilt stage1 driver, 2026-09-16: `reseat_through_conduit` compiled
//! **2 proved, 0 failed** — the value resolver handed back the stale
//! `Range { 0, 5 }`, the yield fact `i < 5` discharged the bounds check, and the
//! program panics `index out of bounds: the len is 5 but the index is 5` at
//! runtime. The gate's operand walk did not see a write whose PLACE is rooted at
//! the conduit, so a migration onto the origin question over the gate as it stood
//! would have proved this program again; the gate now refuses a write rooted at a
//! conduit, and the origin lane declines here exactly as the resolver does.
//!
//! `pesc_nocall` is the modulo shape with the same store and no call at all:
//! also 2 proved on the pristine driver, also a runtime panic (`n % 9` reaches 8
//! on a `[u8; 4]`). Neither may prove. The file is `check-fail` because under
//! strict policy an undischarged Level 0 obligation is a build error — the sound
//! direction for a claim the program violates.

pub fn reseat_through_conduit(a: &[u8; 5]) -> u8 {
    let mut it = 0..5usize;
    let p = &mut it;
    // The write no scan keyed on `it` can see, and the one the conduit gate must
    // refuse: this statement's place-local is `p`.
    *p = 0..100usize;
    let mut s = 0u8;
    for i in it {
        s = s.wrapping_add(a[i]);
    }
    s
}

pub fn pesc_nocall(n: usize, b: &[u8; 4]) -> u8 {
    let mut m = 4usize;
    let p = &mut m;
    *p = 9;
    b[n % m]
}
