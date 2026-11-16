//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 item 18 (shape 1): an argument whose type tree holds a PATTERN TYPE. Every
//! `String`/`Vec` holds one (`RawVec`'s capacity is `UsizeNoHighBit`, a
//! `pattern_type!(usize is 0..=MAX/2)`), and the argument-shape walk read `ty::Pat` as
//! opaque, so `serialize_field(&mut st, "name", &self.name)` — the serde-derive call
//! preview2 counted most (~200 rows across ty/trust-vc/clean) — was refused with "a `&`
//! whose pointee holds a raw pointer or an opaque part" and kept its class (c) `failed`
//! row. A pattern type is its base type's bits under a validity restriction, so it is
//! now shaped AS ITS BASE: `pattern_type!(usize is ..)` is a scalar (`&String`,
//! `&Vec<u32>`, `&Option<String>` and a by-value `String` are inert), and
//! `pattern_type!(*const u8 is !null)` is still a raw pointer (refused).
//!
//! Admitted (one hypothesis row per site, nothing `failed`): `ser_fields` (3 sites),
//! `by_value`. Discharge: `use_good` names `ser_fields::<Good>` (proved, counted
//! skipped), `use_boom` names `ser_fields::<Boom>`, whose `serialize_field` panics —
//! a `failed` discharge row, an error on strict/certify.
//! Controls that stay refused (`failed`, class (c)): `edit_in_place` (`&mut String`:
//! the havoc cannot reach the heap buffer), `raw_pattern` (a `&` to a raw-pointer
//! pattern type), `cells_behind_vec` (`&Vec<Cell<u32>>`: interior mutability behind an
//! owning pointer).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): under `strict` the discharged
//! caller now carries its call's panic-freedom aggregate as one `runtime_checked` row,
//! which `strict` reports rather than fails (it keeps its runtime check), so that
//! caller is no longer a `strict` error; `certify` still refuses it, and every
//! discharge failure and refused control below is unchanged (measured on the merged
//! stage 1).
#![feature(pattern_type_macro, pattern_types)]

use std::cell::Cell;
use std::pat::pattern_type;

pub trait SerializeStruct {
    fn serialize_field<V: ?Sized>(&mut self, key: &'static str, value: &V);
}

pub struct Rec {
    pub name: String,
    pub ids: Vec<u32>,
    pub tag: Option<String>,
}

pub fn ser_fields<S: SerializeStruct>(st: &mut S, r: &Rec) {
    //[advisory]~^ WARN Trust verification advisory for `pattern_type_argument_admitted::ser_fields`: 3 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `pattern_type_argument_admitted::ser_fields`: 3 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `pattern_type_argument_admitted::ser_fields`: 3 instance hypothesis row(s)
    st.serialize_field("name", &r.name);
    st.serialize_field("ids", &r.ids);
    st.serialize_field("tag", &r.tag);
}

pub trait Sink {
    fn take(&self, s: String) -> u32;
}

pub fn by_value<K: Sink>(k: &K, s: String) -> u32 {
    //[advisory]~^ WARN Trust verification advisory for `pattern_type_argument_admitted::by_value`: 1 instance hypothesis row(s)
    //[strict]~^^ WARN Trust verification advisory for `pattern_type_argument_admitted::by_value`: 1 instance hypothesis row(s)
    //[certify]~^^^ ERROR Trust certify verification failed for `pattern_type_argument_admitted::by_value`: 1 instance hypothesis row(s)
    k.take(s)
}

pub struct Good;
pub struct Boom;

impl SerializeStruct for Good {
    fn serialize_field<V: ?Sized>(&mut self, _key: &'static str, _value: &V) {}
}

impl SerializeStruct for Boom {
    fn serialize_field<V: ?Sized>(&mut self, _key: &'static str, _value: &V) {
        //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `<pattern_type_argument_admitted::Boom as pattern_type_argument_admitted::SerializeStruct>::serialize_field`: 2 obligation(s) were not proved
        //[strict]~^^ ERROR Trust strict verification failed for `<pattern_type_argument_admitted::Boom as pattern_type_argument_admitted::SerializeStruct>::serialize_field`: 2 obligation(s) were not fully verified
        //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `<pattern_type_argument_admitted::Boom as pattern_type_argument_admitted::SerializeStruct>::serialize_field`: 2 obligation(s) were not proved
        //[certify]~^^^^ ERROR Trust strict verification failed for `<pattern_type_argument_admitted::Boom as pattern_type_argument_admitted::SerializeStruct>::serialize_field`: 2 obligation(s) were not fully verified
        panic!("boom")
    }
}

pub fn use_good(r: &Rec) {
    // [strict] re-pinned 2026-10-15 (merge of 2026-10-14): `1 runtime-checked`, reported
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::use_good`: 1 obligation(s) were not proved
    //[certify]~^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::use_good`: 1 obligation(s) were not fully verified
    ser_fields(&mut Good, r)
}

pub fn use_boom(r: &Rec) {
    //[advisory]~^ WARN Trust instance discharge not established for `pattern_type_argument_admitted::use_boom`: 3 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `pattern_type_argument_admitted::use_boom`: 3 instance(s)
    //[strict]~^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    //[certify]~^^^^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::use_boom`: 1 obligation(s) were not proved
    //[certify]~^^^^^ ERROR Trust instance discharge not established for `pattern_type_argument_admitted::use_boom`: 3 instance(s)
    //[certify]~^^^^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::use_boom`: 1 obligation(s) were not fully verified
    ser_fields(&mut Boom, r)
}

// Controls: still refused.

pub trait Edit {
    fn edit(&self, s: &mut String);
}

pub fn edit_in_place<E: Edit>(e: &E, s: &mut String) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::edit_in_place`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::edit_in_place`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::edit_in_place`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::edit_in_place`: 1 obligation(s) were not fully verified
    e.edit(s)
}

pub type Nn = pattern_type!(*const u8 is !null);

pub trait TakeNn {
    fn take_nn(&self, p: &Nn);
}

pub fn raw_pattern<K: TakeNn>(k: &K, p: &Nn) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::raw_pattern`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::raw_pattern`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::raw_pattern`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::raw_pattern`: 1 obligation(s) were not fully verified
    k.take_nn(p)
}

pub trait Peek {
    fn peek(&self, v: &Vec<Cell<u32>>);
}

pub fn cells_behind_vec<P: Peek>(p: &P, v: &Vec<Cell<u32>>) {
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::cells_behind_vec`: 1 obligation(s) were not proved
    //[strict]~^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::cells_behind_vec`: 1 obligation(s) were not fully verified
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for `pattern_type_argument_admitted::cells_behind_vec`: 1 obligation(s) were not proved
    //[certify]~^^^^ ERROR Trust strict verification failed for `pattern_type_argument_admitted::cells_behind_vec`: 1 obligation(s) were not fully verified
    p.peek(v)
}
