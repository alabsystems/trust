//@ needs-trust-verify
//@ revisions: admitted admitted_strict admitted_certify
//@ revisions: unwrap index hand_ord hand_ord_foreign_self hand_display skip_drop union_elem
//@ revisions: fn_ptr_field dyn_field hand_send hand_sync hand_unpin
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@[admitted_strict] compile-flags: -Ztrust-policy=strict
//@[admitted_certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[admitted] check-pass
//@[admitted_strict] check-pass
//@[admitted_certify] check-fail
//@[unwrap] check-fail
//@[index] check-fail
//@[hand_ord] check-fail
//@[hand_ord_foreign_self] check-fail
//@[hand_display] check-fail
//@[skip_drop] check-fail
//@[union_elem] check-fail
//@[fn_ptr_field] check-fail
//@[dyn_field] check-fail
//@[hand_send] check-fail
//@[hand_sync] check-fail
//@[hand_unpin] check-fail
#![crate_type = "lib"]
//! VANILLA-REACH-1 (2026-10-27, docs/DECISION_QUEUE.md): a std callee
//! instantiated at a LOCAL plain-data type joins the policy-B vanilla class when
//! CALL-REACH-1 closes the call — its unproved panic row is runtime-checked, as
//! the same call at `String` always was.
//!
//! MEASURED on a stage 1 of main `723f9ec299`: `admitted`'s `get` and `push` were
//! each refused on one "generic absent callee" row (`BTreeMap::<String,
//! Entry>::get::<str>`, `Vec::<(u32, Option<Fate>)>::push`), while the same bodies
//! over `String` values built. The claude-code-alab and agy-alab harnesses lost
//! functions to exactly these rows.
//!
//! The negative revisions are the conjuncts the extension keeps:
//!  * `unwrap`, `index`: a caller-value panic family (`Option::unwrap`, `Index`)
//!    is never taken, whatever the type;
//!  * `hand_ord`, `hand_ord_foreign_self`, `hand_display`: a local type with a
//!    hand-written impl of a sysroot trait outside the law-free allow-list is not
//!    plain data — std relies on `Ord`'s and `Display`'s LAWS (a non-total order,
//!    a formatting impl returning `Err` on its own), which verification of the
//!    impl body does not establish. Even a `Display` the callee never calls keeps
//!    the type out: the rule asks the type, not the callee;
//!  * `skip_drop`: a `#[trust::skip]` destructor is not held, so `clear` (which
//!    drops every element) reaches code nothing verified;
//!  * `union_elem`, `fn_ptr_field`, `dyn_field`: a union, and a field through
//!    which code chosen at run time can run, are not plain data;
//!  * `hand_send`, `hand_sync`, `hand_unpin` (the G2 review's Finding 1): a
//!    hand-written `unsafe impl Send`/`Sync` or `impl Unpin` is not law-free —
//!    breaking it is undefined behaviour in std's synchronization or `Pin` code,
//!    not a panic a verified body carries — so it keeps the type out. `admitted`'s
//!    `push_raw` is the same call at the same `Raw` with NO marker impl, and is
//!    admitted: the marker impl is the only difference between the revisions.
//! `admitted_certify` is the policy control: the admitted rows are
//! runtime-checked, and certify refuses every one.
use std::collections::BTreeMap;

// No `Debug` or `Hash` derive here: each is refused on its own rows (the fmt and
// hasher classes, not this rule), which would hide what the revisions measure.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fate {
    Kept,
    Dropped(u32),
}

#[derive(Clone)]
pub struct Entry {
    pub name: String,
    pub fate: Option<Fate>,
}

#[cfg(any(admitted, admitted_strict, admitted_certify))]
pub fn get(m: &BTreeMap<String, Entry>, k: &str) -> bool {
    //[admitted_certify]~^ ERROR Trust
    m.get(k).is_some()
}

#[cfg(any(admitted, admitted_strict, admitted_certify))]
pub fn push(v: &mut Vec<(u32, Option<Fate>)>, x: u32) {
    //[admitted_certify]~^ ERROR Trust
    v.push((x, None));
}

// A raw pointer is plain data (conjunct 3); with no hand-written marker impl `Raw`
// is `!Send + !Sync`, so nothing can move it to another thread.
#[cfg(any(admitted, admitted_strict, admitted_certify, hand_send, hand_sync, hand_unpin))]
pub struct Raw(pub *const u8);

#[cfg(hand_send)]
unsafe impl Send for Raw {}

#[cfg(hand_sync)]
unsafe impl Sync for Raw {}

#[cfg(hand_unpin)]
impl Unpin for Raw {}

#[cfg(any(admitted, admitted_strict, admitted_certify, hand_send, hand_sync, hand_unpin))]
pub fn push_raw(v: &mut Vec<(u32, Option<Raw>)>, x: u32) {
    //[admitted_certify,hand_send,hand_sync,hand_unpin]~^ ERROR Trust
    v.push((x, None));
}

#[cfg(unwrap)]
pub fn take(o: Option<Fate>) -> Fate {
    //[unwrap]~^ ERROR Trust
    o.unwrap()
}

#[cfg(index)]
pub fn nth(v: &Vec<Entry>, i: usize) -> bool {
    //[index]~^ ERROR Trust
    v[i].fate.is_some()
}

#[cfg(any(hand_ord, hand_ord_foreign_self))]
#[derive(PartialEq, Eq)]
pub struct Key(pub u32);

#[cfg(hand_ord)]
impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(hand_ord)]
impl Ord for Key {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.0.cmp(&self.0)
    }
}

#[cfg(hand_ord)]
pub fn lookup(m: &BTreeMap<Key, u32>, k: u32) -> bool {
    //[hand_ord]~^ ERROR Trust
    m.get(&Key(k)).is_some()
}

// The impl's `Self` is `u32`; the local type is a TRAIT argument. It still names
// `Key`, so `Key` is not plain.
#[cfg(hand_ord_foreign_self)]
impl PartialEq<Key> for u32 {
    fn eq(&self, other: &Key) -> bool {
        *self == other.0
    }
}

#[cfg(hand_ord_foreign_self)]
pub fn push_key(v: &mut Vec<Key>, k: u32) {
    //[hand_ord_foreign_self]~^ ERROR Trust
    v.push(Key(k));
}

#[cfg(hand_display)]
pub struct Name(pub String);

#[cfg(hand_display)]
impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

#[cfg(hand_display)]
pub fn push_name(v: &mut Vec<(u32, Option<Name>)>, x: u32) {
    //[hand_display]~^ ERROR Trust
    v.push((x, None));
}

#[cfg(skip_drop)]
pub struct Guard(pub u32);

#[cfg(skip_drop)]
impl Drop for Guard {
    #[trust::skip]
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("unverified destructor");
        }
    }
}

#[cfg(skip_drop)]
pub fn clear(v: &mut Vec<Guard>) {
    //[skip_drop]~^ ERROR Trust
    v.clear();
}

#[cfg(union_elem)]
#[derive(Clone, Copy)]
pub union Bits {
    pub word: u32,
    pub real: f32,
}

#[cfg(union_elem)]
pub fn push_bits(v: &mut Vec<(u32, Option<Bits>)>, x: u32) {
    //[union_elem]~^ ERROR Trust
    v.push((x, None));
}

#[cfg(fn_ptr_field)]
pub struct Hook {
    pub run: fn(u32) -> u32,
}

#[cfg(fn_ptr_field)]
pub fn push_hook(v: &mut Vec<(u32, Option<Hook>)>, x: u32) {
    //[fn_ptr_field]~^ ERROR Trust
    v.push((x, None));
}

#[cfg(dyn_field)]
pub struct Boxed {
    pub run: Box<dyn Fn(u32) -> u32>,
}

#[cfg(dyn_field)]
pub fn push_boxed(v: &mut Vec<(u32, Option<Boxed>)>, x: u32) {
    //[dyn_field]~^ ERROR Trust
    v.push((x, None));
}
