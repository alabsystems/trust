//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[default] check-pass
//@[certify] compile-flags: -Ztrust-policy=certify
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A bundled std member whose internal Assert divides by a field read through
//! `&self` (`<ChunksExact<_> as Iterator>::size_hint` divides by `self.chunk_size`),
//! or indexes by a computed value (`isqrt`'s `u64_stages`), cannot be charged to a
//! caller. Like the other foundational-member Assert refusals it is std's own
//! runtime check: an advisory warning under the default policy, refused under
//! certify. Before 2026-09-30 these two spellings fell to the generic abort and
//! refused six ChunksExact sweep programs and `m05_isqrt` outright.
pub fn chunks(v: &[u8]) -> usize { //[certify]~ ERROR verification failed
    v.chunks_exact(4).count()
}

pub fn root(x: u64) -> u64 { //[certify]~ ERROR verification failed
    x.isqrt()
}
