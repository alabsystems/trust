//@ revisions: filter_map_collect filter_map_find filter_map_div flat_map_assert
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[filter_map_collect] check-pass
//@[filter_map_find] check-pass
//@[filter_map_div] check-fail
//@[flat_map_assert] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W4 ITER-HOF (a): `filter_map(f)` and `flat_map(f)` over a slice or str
//! iterator are CONSTRUCTORS, exactly like the `map(f)`/`filter(p)` pair the
//! bridge's typed-receiver gate already owned.
//!
//! MEASURED OVER-REFUSAL (unaimed-90, d3/p04 and d4/p03; `rerun/mapctl.rs`):
//! `v.iter().map(|x| ..).collect()` built rc=0 while the byte-for-byte same
//! pipeline spelled `filter_map` was refused. The B-lane declines every
//! protocol method on a total std iterator receiver (`[ENQUEUE_SKIP]
//! gate@line45299`), the bridge's constructor arm named only `map`/`filter`/
//! `cloned`, so `<Iter<_> as Iterator>::filter_map::<_, {closure}>` became an
//! ABSENT callee — and its closure type argument is not foundational, so the
//! row was `NOT-VANILLA` and fatal.
//!
//! In the pinned core both are the trait's provided methods,
//! `FilterMap::new(self, f)` (= `FilterMap { iter, f }`) and
//! `FlatMap::new(self, f)` (= `FlatMap { inner: FlattenCompat::new(iter.map(f)) }`,
//! whose `FlattenCompat::new` is `{ iter: iter.fuse(), frontiter: None,
//! backiter: None }`); no type in core/alloc/std overrides either. The
//! constructor therefore stores the closure and returns — no user code, no
//! panic. The closure runs LATER, inside `FilterMap::next`/`FlatMap::next`,
//! whose own obligations are unchanged: the adapter types are not slice/str
//! iterator receivers, so their advance stays on a bundled body or the
//! fail-closed absent-callee arm.
//!
//! The check-fail revisions are the soundness half: a closure that CAN panic
//! must still refuse the build now that the constructor is no longer the row
//! that refused it. The refusal lands on the CLOSURE, which is verified as its
//! own root; the caller carries the same tolerated closure-consumer row its
//! `map` twin always has (`v.iter().map(|&x| 100 / x).collect()` reports
//! identically), so the pins are on the closure's line.
//!
//! BEFORE (stage-1 snapshot `fb304b993`, two commits behind this branch's base
//! `3b30328c07`; neither intervening commit touches these lanes):
//! `filter_map_collect` and `filter_map_find` were both refused (`NOT-VANILLA callee=<Iter<..> as
//! Iterator>::filter_map::<.., {closure}>`); the two check-fail revisions were
//! refused as well.

#[cfg(filter_map_collect)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().filter_map(|x| x.checked_add(1)).collect()
}

#[cfg(filter_map_find)]
fn parse_pair(line: &str) -> Option<(&str, &str)> {
    let line = line.trim();
    if line.starts_with('#') {
        return None;
    }
    let (key, value) = line.split_once('=')?;
    let key = key.trim();
    if key.is_empty() {
        return None;
    }
    Some((key, value.trim()))
}

#[cfg(filter_map_find)]
pub fn f<'a>(lines: &[&'a str], wanted: &str) -> Option<&'a str> {
    lines.iter().filter_map(|l| parse_pair(l)).find(|(k, _)| *k == wanted).map(|(_, v)| v)
}

// `100 / x` panics at `x == 0`: the constructor admission must not hide it.
#[cfg(filter_map_div)]
pub fn f(v: &[u32]) -> Vec<u32> {
    v.iter().filter_map(|&x| Some(100 / x)).collect()
    //[filter_map_div]~^ ERROR Trust strict verification failed
}

// The closure asserts on its input: `flat_map` over it must stay refused.
#[cfg(flat_map_assert)]
pub fn f(s: &str) -> String {
    s.chars()
        .flat_map(|c| {
            //[flat_map_assert]~^ ERROR Trust strict verification failed
            assert!(c != 'x');
            c.to_lowercase()
        })
        .collect()
}
