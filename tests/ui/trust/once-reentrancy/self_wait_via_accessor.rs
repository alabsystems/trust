//@ check-fail
//@ compile-flags: -Ztrust-verify=off
// ignore-tidy-linelength
//
// Trust: the receiver comes back from an ACCESSOR — `fn cell() -> &'static
// OnceLock<..>` — instead of naming the static directly. A call destination has
// no assignment statement, so the receiver walk follows the callee into its
// return place; without that, both shapes below compiled (round-1 finding) and
// deadlock at runtime exactly like the direct aterm shape. Both the
// fn-local-static accessor and a `const fn` accessor over a module static are
// covered.

#![allow(dead_code)]

use std::sync::OnceLock;

fn cell() -> &'static OnceLock<bool> {
    static ARMED: OnceLock<bool> = OnceLock::new();
    &ARMED
}

pub fn armed() -> bool {
    *cell().get_or_init(|| armed())
    //~^ ERROR the initializer of `ARMED` can wait on `ARMED` itself
}

static SEEDED: OnceLock<u32> = OnceLock::new();

const fn seeded_cell() -> &'static OnceLock<u32> {
    &SEEDED
}

pub fn seeded() -> u32 {
    *seeded_cell().get_or_init(|| seeded() + 1)
    //~^ ERROR the initializer of `SEEDED` can wait on `SEEDED` itself
}

fn main() {
    let _ = armed();
    let _ = seeded();
}
