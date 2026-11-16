//@ edition: 2021
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **The Seq-lane grow summary is the pinned INSTANCE, not a name.**
//!
//! Only `<Vec<u8, Global>>::extend_from_slice` carries the compiler's pinned
//! identity. Another element type (`u16`: byte length is not element length), a
//! call at a type parameter (no identity at all), and a user method spelled
//! `extend_from_slice` keep the honest row, so certify refuses each of them
//! (MEASURED on the stage 1 of this change and the one before it: identical).
//! The positive twin is `vec_u8_extend_from_slice_seq_axiom.rs`.

pub fn grow_u16(v: &mut Vec<u16>, s: &[u16]) {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    v.extend_from_slice(s)
}

pub fn grow_generic<T: Clone>(v: &mut Vec<T>, s: &[T]) {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    v.extend_from_slice(s)
}

pub struct Sink(pub Vec<u8>);

impl Sink {
    pub fn extend_from_slice(&mut self, s: &[u8]) {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        if s.len() == 3 {
            panic!("not std");
        }
        self.0.clear();
    }
}

pub fn grow_user(v: &mut Sink, s: &[u8]) {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    v.extend_from_slice(s)
}
