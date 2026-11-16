// Trust (LEN-KEY-1, 2026-10-06): std's `Vec` length and index survive the
// `::<__trust_args@…>` tag of a DUPLICATE-CRATE-NAME graph; user `len`/`index`
// methods stay refused in the same graph.
//
// The tag. `trust_mir_extract::convert::disambiguate_generic_call_path` appends
// `::<__trust_args@HASH>` to EVERY generic callee when any two crates of the graph
// share a name. An ordinary Cargo graph does: a crates.io `memchr` (pulled in by
// `serde_json`) shares its name with the `memchr` std itself depends on. So in
// ty's `tla-cert` std's `Vec::len` is `alloc::vec::Vec::<T>::len::<__trust_args@…>`
// and its index `<alloc::vec::Vec<T> as core::ops::index::Index<usize>>::index
// ::<__trust_args@…>`. NAME-ANCHOR-1 (35a45d66a3) replaced the length-of-place
// recognizers' tag-tolerant `method_tail(callee) == "len"` with the exact matcher of
// the `_len == coll_len` tie site, which had always declined the tag. With both
// declining it, 29 `args[k]` rows of `tla-cert` (`axiom_check.rs`:
// `args.len() == 2 && args[0] == Term::Int(0)`) went `slice proved` -> `slice
// failed` (the 10-03 preview's stage 1 `5424ce87e` vs the stage 1 of `c797f90c1`;
// bisected at the trust-vcgen level on this file's `formula_field` dump: proved at
// `35a45d66a3^`, failed at `35a45d66a3`). The fix (LEN-KEY-1) admits std's inherent
// `len` by its DefId key at the tie site and at the three recognizers.
//
// FIXTURES: `fixtures/dup_crate_name_len_tie/`, one function per file, dumped
// (`-Ztrust-dump=mir:<dir>`) by the stage 1 of `c797f90c1` from the source below,
// compiled as `dup_len_tie.rs` with `--crate-type=lib --edition=2021
// -Ztrust-verify=on -Ztrust-policy=advisory --extern memchr=<crates.io memchr 2.x
// rmeta>`. That compiler, on that graph, reported every `slice` row of
// `formula_field`, `plain_tie`, `field_good` and `std_vec_index_twice` FAILED; on the
// source WITHOUT the `memchr` call and the generic twins (a unique graph, no tag) it
// reported all of them proved. Every lie (`*_user_*`, `two_user_*`) read `failed` in
// the tagged graph, and the non-generic ones in the unique graph too.
//
// ```ignore (source of the fixtures; `pub fn touch` is what loads `memchr`)
// use core::ops::Index;
// pub fn touch(h: &[u8]) -> Option<usize> { memchr::memchr(b'a', h) }
// #[derive(PartialEq)]
// pub enum Term { Int(i64), App(String, Vec<Term>) }
// pub enum Formula { Eq(Term, Term), Other }
// pub fn formula_field(formula: &Formula) -> bool {
//     if let Formula::Eq(Term::App(op, args), rhs) = formula {
//         if op == "+" && args.len() == 2 && args[0] == Term::Int(0) && &args[1] == rhs {
//             return true;
//         }
//     }
//     false
// }
// pub fn plain_tie(v: &Vec<u32>) -> u32 { if v.len() == 2 { v[1] } else { 0 } }
// pub struct W { pub v: Vec<u32> }
// pub fn field_good(w: &W, j: usize) -> u32 { if j < w.v.len() { w.v[j] } else { 0 } }
// pub trait L { fn len(&self) -> usize; }
// impl L for Vec<u32> { fn len(&self) -> usize { Vec::len(self).saturating_add(5) } }
// pub fn field_user_len(w: &W, j: usize) -> u32 { if j < L::len(&w.v) { w.v[j] } else { 0 } }
// pub fn plain_user_len(v: &Vec<u32>) -> u32 { if L::len(v) == 2 { v[1] } else { 0 } }
// static ZERO: u32 = 0;
// static MAX: u32 = u32::MAX;
// pub struct A;
// pub struct B;
// impl Index<A> for [u32] { type Output = u32; fn index(&self, _k: A) -> &u32 { &ZERO } }
// impl Index<B> for [u32] { type Output = u32; fn index(&self, _k: B) -> &u32 { &MAX } }
// pub fn two_user_index_keys(v: &[u32]) -> u32 {
//     let a = v[A]; let b = v[B]; if a == 0 { b + 1 } else { 0 }
// }
// pub fn std_vec_index_twice(v: &Vec<u32>, i: usize) -> u32 {
//     if i < v.len() && v[i] < 10 { v[i] + 1 } else { 0 }
// }
// // Generic local impls are not devirtualized: the trait spelling AND the tag survive.
// pub trait GL { fn len(&self) -> usize; }
// impl<T> GL for Vec<T> { fn len(&self) -> usize { Vec::len(self).saturating_add(5) } }
// pub fn field_user_generic_len(w: &W, j: usize) -> u32 { if j < GL::len(&w.v) { w.v[j] } else { 0 } }
// pub fn plain_user_generic_len(v: &Vec<u32>) -> u32 { if GL::len(v) == 2 { v[1] } else { 0 } }
// pub struct GA<T>(pub T);
// pub struct GB<T>(pub T);
// impl<T> Index<GA<T>> for [u32] { type Output = u32; fn index(&self, _k: GA<T>) -> &u32 { &ZERO } }
// impl<T> Index<GB<T>> for [u32] { type Output = u32; fn index(&self, _k: GB<T>) -> &u32 { &MAX } }
// pub fn two_user_generic_index_keys(v: &[u32]) -> u32 {
//     let a = v[GA(())]; let b = v[GB(())]; if a == 0 { b + 1 } else { 0 }
// }
// ```
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
use trust_types::{
    BinOp, Terminator, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/dup_crate_name_len_tie/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// `(interval-discharged count, routed verdicts)` for `func`'s rows of one kind.
fn rows(
    func: &VerifiableFunction,
    is_kind: impl Fn(&VerificationCondition) -> bool,
) -> (usize, Vec<VerificationResult>) {
    let (solver, discharged) = trust_vcgen::generate_vcs_with_discharge(func);
    let r = router();
    let routed: Vec<VerificationResult> =
        solver.iter().filter(|vc| is_kind(vc)).map(|vc| r.verify_one(vc)).collect();
    (discharged.iter().filter(|(vc, _)| is_kind(vc)).count(), routed)
}

fn is_slice(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::SliceBoundsCheck)
}

fn is_add(vc: &VerificationCondition) -> bool {
    matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

/// Every `func` callee spelled with the duplicate-crate-name tag, so a fixture
/// regenerated in a unique graph (no tag) fails here instead of passing vacuously.
fn tagged_callees(func: &VerifiableFunction) -> Vec<&str> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, .. } if callee.contains("::<__trust_args@") => {
                Some(callee.as_str())
            }
            _ => None,
        })
        .collect()
}

#[test]
fn std_vec_len_and_index_prove_in_a_duplicate_crate_name_graph() {
    // (fixture, slice rows it mints). Each row is proved, by the interval lane or ay.
    for (name, n) in
        [("formula_field", 2), ("plain_tie", 1), ("field_good", 1), ("std_vec_index_twice", 2)]
    {
        let func = load(name);
        assert!(
            tagged_callees(&func).iter().any(|c| c.contains("::len::<__trust_args@")),
            "{name}: vacuity guard, std's `len` carries the tag"
        );
        let (discharged, routed) = rows(&func, is_slice);
        assert_eq!(discharged + routed.len(), n, "{name}: vacuity guard, {n} slice row(s)");
        assert!(
            routed.iter().all(is_proved),
            "{name}: std's `Vec::len` bounds std's `Vec` index whatever the tag: {routed:?}"
        );
    }
}

#[test]
fn a_user_len_stays_refused_in_a_duplicate_crate_name_graph() {
    // NAME-ANCHOR-1's lie: `L::len` over-reports by 5. Non-generic (devirtualized, no
    // tag) and generic (trait spelling, tagged) both; whole `&Vec` and struct field.
    for name in
        ["field_user_len", "plain_user_len", "field_user_generic_len", "plain_user_generic_len"]
    {
        let func = load(name);
        let (discharged, routed) = rows(&func, is_slice);
        assert_eq!(discharged, 0, "{name}: no interval proof of the index");
        assert_eq!(routed.len(), 1, "{name}: vacuity guard, the slice row is minted");
        assert!(
            !routed.iter().any(is_proved),
            "{name}: a user `len` is not the `Vec`'s length: {routed:?}"
        );
    }
    assert!(
        tagged_callees(&load("plain_user_generic_len"))
            .iter()
            .any(|c| c.contains(" as dup_len_tie::GL>::len::<__trust_args@")),
        "vacuity guard: the generic user `len` reaches vcgen tagged, like std's"
    );
}

#[test]
fn user_index_keys_stay_refused_in_a_duplicate_crate_name_graph() {
    // IDX-TIE-1's lie: `v[A]` reads 0 and `v[B]` reads u32::MAX, so `b + 1` overflows.
    for name in ["two_user_index_keys", "two_user_generic_index_keys"] {
        let (discharged, routed) = rows(&load(name), is_add);
        assert_eq!(discharged, 0, "{name}");
        assert_eq!(routed.len(), 1, "{name}: vacuity guard, the `b + 1` row is minted");
        assert!(
            !routed.iter().any(is_proved),
            "{name}: two user `Index` impls are two different reads: {routed:?}"
        );
    }
    assert_eq!(
        tagged_callees(&load("two_user_generic_index_keys")).len(),
        2,
        "vacuity guard: both generic user `index` calls reach vcgen tagged"
    );
}

#[test]
fn the_len_key_is_what_proves_the_whole_vec_tie() {
    // `plain_tie`'s tie reads std's `len` by its DefId key (the string is tagged).
    // Strip the key, or mark its crate not the resident sysroot, and the tie is gone.
    for mutate in [(|k: &mut Option<trust_types::CalleeKey>| *k = None) as fn(&mut _), |k| {
        if let Some(k) = k.as_mut() {
            k.krate_is_real_sysroot = false;
        }
    }] {
        let mut func = load("plain_tie");
        let mut touched = 0;
        for b in &mut func.body.blocks {
            if let Terminator::Call { func: callee, callee_key, .. } = &mut b.terminator
                && callee.starts_with("alloc::vec::Vec::<u32>::len::<__trust_args@")
            {
                mutate(callee_key);
                touched += 1;
            }
        }
        assert_eq!(touched, 1, "vacuity guard: one std `len` call");
        let (discharged, routed) = rows(&func, is_slice);
        assert_eq!(discharged, 0);
        assert!(
            !routed.iter().any(is_proved),
            "an unkeyed tagged `len` is not trusted as std's: {routed:?}"
        );
    }
}
