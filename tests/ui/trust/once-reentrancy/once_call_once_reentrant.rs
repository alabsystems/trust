//@ check-fail
//@ compile-flags: -Ztrust-verify=off
// ignore-tidy-linelength
//
// Trust: the raw `std::sync::Once`. `call_once` inside its own `call_once`
// closure parks forever; the via-fn form (`P.call_once(body_p)`, where `body_p`
// calls `P.call_once` again) is the same defect one call away.

#![allow(dead_code)]

use std::sync::Once;

static O: Once = Once::new();

fn init_o() {
    O.call_once(|| {
        O.call_once(|| ());
        //~^ ERROR the initializer of `O` can wait on `O` itself: a `std::sync::Once` initializer that re-enters its own cell deadlocks
    })
}

static P: Once = Once::new();

fn init_p() {
    P.call_once(body_p)
}

fn body_p() {
    P.call_once(|| ());
    //~^ ERROR the initializer of `P` can wait on `P` itself
}

fn main() {
    init_o();
    init_p();
}
