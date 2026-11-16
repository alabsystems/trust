//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `peek_borrow_keeps_the_iterator_instance_fixed.rs`: the `&mut` borrow
//! reaches a function that replaces the iterator, so on a non-empty slice the loop
//! never ends and the counter overflows.
use std::iter::Peekable;
use std::slice::Iter;

fn rewind<'a>(p: &mut Peekable<Iter<'a, u32>>, v: &'a [u32]) {
    *p = v.iter().peekable();
}

pub fn spin(v: &[u32]) -> usize { //~ ERROR verification
    let mut it = v.iter().peekable();
    let mut n = 0usize;
    while let Some(_) = it.next() {
        n += 1;
        if it.peek().is_none() {
            rewind(&mut it, v);
        }
    }
    n
}
