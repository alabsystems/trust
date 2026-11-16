//@ revisions: default strict certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! A length tie through `Deref` is std's theorem about std's `Vec` and `String`, not
//! about every type that implements std's `Deref` trait (DEREF-ANCHOR-1).
//!
//! `guards::base_collection_step` traces a receiver back to its base collection so
//! that every `.len()` on that base reads one `coll_len(base)`. It hopped any
//! `deref`/`deref_mut` call whose TRAIT path is std's (`callee_is_std_ops_method`),
//! so it also hopped `<…::Wrap as core::ops::deref::Deref>::deref`, a user impl. rustc
//! keys that call on core's `Deref::deref` trait-method DefId, so the call's
//! `callee_key` names core and not the impl that runs. `Wrap`'s `deref` returns
//! `&self.a` and `&self.b` on alternate calls, so the two `w.len()` in `h` read two
//! different `Vec`s, yet both were tied to one `coll_len(w)`. The `w.len() == 0`
//! guard then discharged `w.len() - 1`: the row read `overflow:sub` proved,
//! Clean-kernel Certified, and the overflow check was elided. With `a = vec![7]` and
//! `b = Vec::new()` the program returns `18446744073709551615` where vanilla Rust
//! panics (the run twin, `deref_len_tie_requires_std_self_run.rs`). `s_len` is the
//! same with `Target = String`; `outer_len` goes through two user hops,
//! `Outer -> Wrap -> Vec`.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, 2026-10-04; each
//! revision's flags with `--emit=metadata`): every revision built exit 0 with no
//! diagnostic at all. `h`, `s_len` and `outer_len` each read `overflow:sub` proved
//! plus an `assert` row proved, and `TRUST_ELIDE_DEBUG=1` printed `elided 1
//! kernel-certified overflow checks` in each, so none of the annotations below fired.
//! The wave-12 scout measured `h` the same way on `stage1-w10` and `stage1-w11`; the
//! lie predates wave 11.
//!
//! AFTER (the fix; predicted, then measured): the hop requires a callee spelled exactly as
//! std's own `Vec`/`String` `Deref`/`DerefMut` AND a receiver whose MIR pointee type is
//! `Ty::Seq` (std's `Vec`), std's `Vec` or std's `String` by exact path. A user
//! `deref` result is its own base, the two `len()` results are untied, and each
//! overflow row is refuted. The annotations are what the BEFORE compiler prints for a
//! twin of this file in which the second `len()` in each lie function reads a SECOND
//! parameter of the same type (`h(w: &Wrap, w2: &Wrap) { if w.len() == 0 { return 0; }
//! w2.len() - 1 }`), which no tie connects even before the fix: in every revision each
//! of the three functions then reads `overflow:sub` failed (ay-in-process) and `assert`
//! runtime-checked, "2 obligation(s) were not proved". A second twin, `h` calling a
//! user trait method named `deref` (`MyDeref::deref(w).len()`, which the old
//! crate-root test already refused), printed the same diagnostics for `h`. The
//! trust-vcgen unit rows (`guards_deref_hop_anchor_tests.rs`) run this file's
//! extracted MIR through vcgen and the in-process ay: the three user rows are not
//! proved after the fix, and were proved before it. Measured on the stage 1 of
//! `ee3f51541d` (2026-10-04): every annotation below fires in every revision, nothing
//! else is reported, and each lie function's `overflow:sub` reads failed.
//!
//! The controls carry no annotation and stay proved in every revision, BEFORE and in
//! both twins: a std `&Vec<u32>` (`std_vec`), std's own `Vec` and `String` `Deref`
//! (`std_vec_view`, `std_string_view`, whose rows need the hop the fix keeps), and the
//! field `w.a` of a user wrapper (`field`), which never crosses a `deref`.

use std::cell::Cell;
use std::ops::Deref;

// A user `Deref` to std's `Vec` that returns a DIFFERENT `Vec` on every call.
pub struct Wrap {
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub flip: Cell<bool>,
}

impl Deref for Wrap {
    type Target = Vec<u32>;
    fn deref(&self) -> &Vec<u32> {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn h(w: &Wrap) -> usize {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::h`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `deref_len_tie_requires_std_self::h`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::h`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `deref_len_tie_requires_std_self::h`
    if w.len() == 0 {
        return 0;
    }
    w.len() - 1
}

// The same with std's `String` as the target.
pub struct S {
    pub a: String,
    pub b: String,
    pub flip: Cell<bool>,
}

impl Deref for S {
    type Target = String;
    fn deref(&self) -> &String {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn s_len(w: &S) -> usize {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::s_len`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `deref_len_tie_requires_std_self::s_len`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::s_len`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `deref_len_tie_requires_std_self::s_len`
    if w.len() == 0 {
        return 0;
    }
    w.len() - 1
}

// Two user hops: `Outer` -> `Wrap` -> `Vec`.
pub struct Outer {
    pub inner: Wrap,
}

impl Deref for Outer {
    type Target = Wrap;
    fn deref(&self) -> &Wrap {
        &self.inner
    }
}

pub fn outer_len(o: &Outer) -> usize {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::outer_len`: 2 obligation(s) were not proved
    //[default,strict,certify]~^^ ERROR Trust strict verification failed for `deref_len_tie_requires_std_self::outer_len`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `deref_len_tie_requires_std_self::outer_len`: 2 obligation(s) were not proved
    //[memsafe]~^^^^ ERROR Trust memory-safe verification failed for `deref_len_tie_requires_std_self::outer_len`
    if o.len() == 0 {
        return 0;
    }
    o.len() - 1
}

// Controls: std's own receivers and std's own `Deref`, which still prove.
pub fn std_vec(v: &Vec<u32>) -> usize {
    if v.len() == 0 { 0 } else { v.len() - 1 }
}

pub fn std_vec_view(v: &Vec<u32>) -> usize {
    if v.len() == 0 {
        return 0;
    }
    let t: &[u32] = v;
    t.len() - 1
}

pub fn std_string_view(s: &String) -> usize {
    if s.len() == 0 {
        return 0;
    }
    let t: &str = s;
    t.len() - 1
}

pub fn field(w: &Wrap) -> usize {
    if w.a.len() == 0 {
        return 0;
    }
    w.a.len() - 1
}
