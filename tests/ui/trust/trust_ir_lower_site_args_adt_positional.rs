//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-AA: `SiteTy::Adt` carried `Vec<SiteTy>`, which cannot record that
// argument *k* of an ADT was a LIFETIME or a CONST — so `encode_ty` had
// to refuse the whole call site whenever an ADT arg was either, and the
// callee identity failed closed (`Callee(MIR site args unencodable)` /
// `Callee(concrete instance args unencodable)`). `TRUST_ENCTY_TRACE`
// measured that as 15 + 4 of the refusals in
// reports/encode-site-args-vocabulary-2026-09-01.md.
//
// It was never a missing capability: `SiteArg` already spells both AT THE
// TOP LEVEL under exactly the arguments that apply here one level deeper
// — `ErasedRegion` is region-blind because the comparator erases regions
// on BOTH sides before pinning identity, and `Const` is intern-equal
// because a `ConstKind::Value` is a re-materializable (type, valtree)
// pair. The payload is now `Vec<SiteArg>`, rebuilt kind-by-kind at each
// position.
//
// DIGEST DISCIPLINE (wave-CRT, which link 2c's pinned digests depend on):
// the ADT arg byte stream is SELF-DISCRIMINATING and byte-compatible — a
// type arg emits its own tag (0..=11), so an ADT whose args are all types
// encodes byte-identically to before this wave and its digest does not
// move; a lifetime is the reserved tag 12 and a const the reserved 13,
// neither producible by the type encoder.

pub struct Holder<'a> {
    pub r: &'a i64,
}

pub struct Sized2<const N: usize> {
    pub v: [i64; N],
}

fn consume<T>(_t: T) -> i64 {
    0
}

// An ADT with a LIFETIME arg in the call's generic args: the site whose
// identity could not be pinned before.
pub fn call_with_lifetime_adt(h: Holder<'_>) -> i64 {
    consume::<Holder<'_>>(h)
}

// An ADT with a CONST arg, likewise.
pub fn call_with_const_adt(s: Sized2<3>) -> i64 {
    consume::<Sized2<3>>(s)
}

// Both kinds nested inside a further ADT arg — the recursion must carry
// each arg at its own kind all the way down.
pub fn call_with_nested(h: Option<Holder<'_>>, s: Option<Sized2<2>>) -> i64 {
    consume::<Option<Holder<'_>>>(h) + consume::<Option<Sized2<2>>>(s)
}

fn main() {}
