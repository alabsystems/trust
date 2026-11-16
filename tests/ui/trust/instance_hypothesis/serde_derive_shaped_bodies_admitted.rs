//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=human --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[certify] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18, end to end: the bodies `#[derive(Deserialize)]` emits for
//! `struct Rec { name: String, n: u32 }`, written out against a local copy of serde's
//! data-model traits (a UI test cannot depend on serde). On main every one of them kept
//! a class (c) `failed` row, named after its first fold site (`next_element::<String>`,
//! `deserialize_struct::<RecVisitor>`, `invalid_value`), but refused for other reasons:
//! * `visit_seq`: the body coerces `&"struct Rec with 2 elements"` to `&dyn Expected`;
//!   D33's census counted that unsizing coercion as an unsafe operation, so the BODY
//!   admitted no site (item 18 shape 3), and the `invalid_length` argument itself is a
//!   trait object (shape 2);
//! * `deserialize`: the by-value visitor `RecVisitor { marker: PhantomData<Rec> }`
//!   reaches `Rec -> String -> Vec -> RawVec -> RawVecInner -> Unique<u8> -> u8`, past
//!   the shape walk's depth cap of 8, and `RawVec`'s capacity is a pattern type
//!   (shape 1);
//! * `visit_u64`: `invalid_value(Unexpected::Unsigned(v), &"variant index 0 <= i < 2")`,
//!   the census arm and the trait-object argument again.
//! All three now carry only hypothesis rows (nothing `failed`). (`visit_seq` is written
//! the way serde's `tri!` expands: the `Result` is bound before the `Option` is matched.
//! A nested `Ok(Some(v))` pattern over a `Result` whose error type is a projection is
//! still refused at the body by the census's type walk — a different census arm, not
//! widened here.) A concrete instance
//! that panics in `invalid_length` (`Boom`) is charged a `failed` discharge row at
//! `use_boom`; `use_fine` reads its discharge `proved` (counted skipped). Human output
//! only: the JSON rows of these bodies exceed compiletest's 512 KiB capture, which
//! silently drops diagnostics from the middle of the stream.
//!
//! `certify` runs with `TRUST_NO_SYSROOT_CENSUS=1` (2026-10-08, std-absent-callee):
//! the sysroot panic census derives `<String as Default>::default` (`String::new`)
//! panic-free, which certifies `<Rec as Default>::default`, the refusal pinned below.
//! This file measures instance hypotheses; withholding the census (it only removes
//! proof) keeps that pin.
use std::marker::PhantomData;

pub trait Expected {
    fn show(&self) -> usize;
}

impl Expected for &str {
    fn show(&self) -> usize {
        self.len()
    }
}

pub enum Unexpected<'a> {
    Unsigned(u64),
    Str(&'a str),
}

pub trait Error: Sized {
    fn invalid_length(len: usize, exp: &dyn Expected) -> Self;
    fn invalid_value(unexp: Unexpected<'_>, exp: &dyn Expected) -> Self;
}

pub trait SeqAccess {
    type Error: Error;
    fn next_element<T: Default>(&mut self) -> Result<Option<T>, Self::Error>;
}

pub trait Visitor: Sized {
    type Value;
}

pub trait Deserializer: Sized {
    type Error: Error;
    fn deserialize_struct<V: Visitor>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>;
}

#[derive(Default)]
// Re-pinned 2026-10-15 (the merge of 2026-10-14): still refused under certify, now by
// ZERO-ROW-GATE (the body publishes no row of its own, and with the census withheld no
// registry it reads discharges `<String as Default>::default`), which reports only the strict
// line; the "incomplete" line came from the unproved row the body used to carry.
//[certify]~^^^^^ ERROR Trust strict verification failed for `<serde_derive_shaped_bodies_admitted::Rec as core::default::Default>::default`: 1 obligation(s) were not fully verified
pub struct Rec {
    pub name: String,
    pub n: u32,
}

pub struct RecVisitor {
    pub marker: PhantomData<Rec>,
}

impl Visitor for RecVisitor {
    type Value = Rec;
}

pub fn visit_seq<A: SeqAccess>(mut seq: A) -> Result<Rec, A::Error> {
    //[advisory]~^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::visit_seq`: 4 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::visit_seq`: 4 instance hypothesis row(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `serde_derive_shaped_bodies_admitted::visit_seq`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `serde_derive_shaped_bodies_admitted::visit_seq`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust certify verification failed for `serde_derive_shaped_bodies_admitted::visit_seq`: 4 instance hypothesis row(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `serde_derive_shaped_bodies_admitted::visit_seq`: 1 obligation(s) were not fully verified
    // serde's `tri!` binds the `Result` first, then matches the `Option`.
    let name = match seq.next_element::<String>() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let name = match name {
        Some(v) => v,
        None => return Err(A::Error::invalid_length(0, &"struct Rec with 2 elements")),
    };
    let n = match seq.next_element::<u32>() {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let n = match n {
        Some(v) => v,
        None => return Err(A::Error::invalid_length(1, &"struct Rec with 2 elements")),
    };
    Ok(Rec { name, n })
}

pub fn deserialize<D: Deserializer>(d: D) -> Result<Rec, D::Error> {
    //[advisory]~^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::deserialize`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::deserialize`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `serde_derive_shaped_bodies_admitted::deserialize`: 1 instance hypothesis row(s)
    d.deserialize_struct("Rec", &["name", "n"], RecVisitor { marker: PhantomData })
}

pub fn visit_u64<E: Error>(v: u64) -> Result<u8, E> {
    //[advisory]~^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::visit_u64`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `serde_derive_shaped_bodies_admitted::visit_u64`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `serde_derive_shaped_bodies_admitted::visit_u64`: 1 instance hypothesis row(s)
    match v {
        0 => Ok(0),
        1 => Ok(1),
        _ => Err(E::invalid_value(Unexpected::Unsigned(v), &"variant index 0 <= i < 2")),
    }
}

pub struct Fine;
pub struct Boom;

impl Error for Fine {
    fn invalid_length(_len: usize, _exp: &dyn Expected) -> Self {
        Fine
    }
    fn invalid_value(_unexp: Unexpected<'_>, _exp: &dyn Expected) -> Self {
        Fine
    }
}

impl Error for Boom {
    fn invalid_length(_len: usize, _exp: &dyn Expected) -> Self {
        Boom
    }
    fn invalid_value(_unexp: Unexpected<'_>, _exp: &dyn Expected) -> Self {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<serde_derive_shaped_bodies_admitted::Boom as serde_derive_shaped_bodies_admitted::Error>::invalid_value`: 2 obligation(s) were not proved
        //[strict]~^^ ERROR Trust strict verification failed for `<serde_derive_shaped_bodies_admitted::Boom as serde_derive_shaped_bodies_admitted::Error>::invalid_value`: 2 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<serde_derive_shaped_bodies_admitted::Boom as serde_derive_shaped_bodies_admitted::Error>::invalid_value`: 2 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<serde_derive_shaped_bodies_admitted::Boom as serde_derive_shaped_bodies_admitted::Error>::invalid_value`: 2 obligation(s) were not fully verified
        panic!("boom")
    }
}

pub fn use_fine(v: u64) -> Result<u8, Fine> {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete for `serde_derive_shaped_bodies_admitted::use_fine`: 1 obligation(s) were not proved
    //[certify]~^^ ERROR Trust strict verification failed for `serde_derive_shaped_bodies_admitted::use_fine`: 1 obligation(s) were not fully verified
    visit_u64::<Fine>(v)
}

pub fn use_boom(v: u64) -> Result<u8, Boom> {
    //[advisory]~^ WARN Trust instance discharge not established for `serde_derive_shaped_bodies_admitted::use_boom`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `serde_derive_shaped_bodies_admitted::use_boom`: 1 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `serde_derive_shaped_bodies_admitted::use_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `serde_derive_shaped_bodies_admitted::use_boom`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `serde_derive_shaped_bodies_admitted::use_boom`: 1 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `serde_derive_shaped_bodies_admitted::use_boom`: 1 obligation(s) were not fully verified
    visit_u64::<Boom>(v)
}
