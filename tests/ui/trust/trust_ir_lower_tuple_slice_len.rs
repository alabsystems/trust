//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-TSL): a `&[T]` TUPLE ELEMENT tested by LENGTH.
//!
//! The tuple/struct/array arm carriers are FLAT and depth-1 and their test
//! channel is equality on the element's own scalar value — that missing
//! representation is what `TupleMatch(nested subpattern)` names. This wave buys
//! back exactly one nested spelling: a slice pattern under a `Deref` on a
//! slice-fat element, whose whole content is a LENGTH fact, which fits the flat
//! carrier once the carrier can say `>=` as well as `==`.
//!
//! `run-pass` is the point: `[]` vs `[_, ..]` vs `[.., _]` all reduce to length
//! tests, and picking the wrong comparison or the wrong constant shows up here
//! as the wrong ARM being taken, not as a changed tag.
//!
//! A rest pattern that BINDS stays fail-closed (`bind_rest_declines`): minting a
//! sub-slice fat value into the flat `binds` carrier is out of scope for this
//! lane — wave-SLM does it at the SCRUTINEE position, where the carrier is not
//! flat. That body must still compute correctly, which main checks.

pub fn match_vecs<'a, T>(l1: &'a [T], l2: &'a [T]) -> &'static str {
    match (l1, l2) {
        (&[], &[]) => "both empty",
        (&[], &[..]) | (&[..], &[]) => "one empty",
        (&[..], &[..]) => "both non-empty",
    }
}

pub fn match_vecs_cons<'a, T>(l1: &'a [T], l2: &'a [T]) -> &'static str {
    match (l1, l2) {
        (&[], &[]) => "both empty",
        (&[], &[_, ..]) | (&[_, ..], &[]) => "one empty",
        (&[_, ..], &[_, ..]) => "both non-empty",
    }
}

pub fn match_vecs_snoc<'a, T>(l1: &'a [T], l2: &'a [T]) -> &'static str {
    match (l1, l2) {
        (&[], &[]) => "both empty",
        (&[], &[.., _]) | (&[.., _], &[]) => "one empty",
        (&[.., _], &[.., _]) => "both non-empty",
    }
}

/// An exact-length test on both elements — `Eq`, not `Uge`.
pub fn exact_two(l1: &[u8], l2: &[u8]) -> u32 {
    match (l1, l2) {
        (&[_, _], &[_]) => 21,
        (&[_, _], &[..]) => 20,
        _ => 0,
    }
}

/// The fence: a rest pattern that BINDS keeps the refusal, and must still be right.
pub fn bind_rest_declines(l: &[u8]) -> usize {
    match (l, 0u8) {
        (&[_, ref rest @ ..], _) => rest.len(),
        _ => 99,
    }
}

fn main() {
    let e: &[u8] = &[];
    let one: &[u8] = &[1];
    let two: &[u8] = &[1, 2];
    assert_eq!(match_vecs(e, e), "both empty");
    assert_eq!(match_vecs(e, one), "one empty");
    assert_eq!(match_vecs(one, e), "one empty");
    assert_eq!(match_vecs(one, two), "both non-empty");
    assert_eq!(match_vecs_cons(e, e), "both empty");
    assert_eq!(match_vecs_cons(e, one), "one empty");
    assert_eq!(match_vecs_cons(two, one), "both non-empty");
    assert_eq!(match_vecs_snoc(e, e), "both empty");
    assert_eq!(match_vecs_snoc(one, e), "one empty");
    assert_eq!(match_vecs_snoc(two, one), "both non-empty");
    assert_eq!(exact_two(two, one), 21);
    assert_eq!(exact_two(two, two), 20);
    assert_eq!(exact_two(one, one), 0);
    assert_eq!(bind_rest_declines(two), 1);
    assert_eq!(bind_rest_declines(e), 99);
}
