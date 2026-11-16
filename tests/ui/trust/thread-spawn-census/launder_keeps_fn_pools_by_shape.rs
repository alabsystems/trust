//@ revisions: laundered handed back reshaped typed
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[laundered] forbid-output:may run a callable of its key that reaches a std thread spawn; effect is unmodeled (fail-closed; not a spawn claim) (via launch
//@[typed] forbid-output:may spawn (indirect)
//! Spawn census (design §5.4 LAUNDER, §13 "one fixture per leg"; P2m cost 4):
//! a cast or transmute that turns a function pointer held in a value's own
//! bytes into something no function pointer of a matching shape holds (`f as
//! usize`, a transmute to another call shape) is a LAUNDER, and plain data may
//! then hold the callable it laundered.
//!
//! * `laundered`: one fn item's address read as an integer (foldhash's global
//!   seed) used to merge every FnPool into one, so `call_u8`'s `fn(u8)` call
//!   reached `launch`. A call is now charged only with its own shape's pool:
//!   calling `launch` through a `fn(u8)` is undefined behaviour (R4), whatever
//!   happened to the pointer. No row is an indirect call or hand-off whose
//!   witness starts at `launch`. (`call_u8` and `launch` are still INDIRECT
//!   through std's panic and drop paths, which hand plain data to code out of
//!   sight, and plain data may hold any callable once a value LAUNDER exists.)
//! * `handed`: the same LAUNDER, and an integer handed to C. A value
//!   LAUNDER is a LAUNDER of `Any` (value LAUNDERs are not keyed yet, design
//!   §10 "Typed LAUNDER", SC-7f), so laundered data may hold ANY callable, not
//!   only `seed_source`, the item it was made from. So C may call `launch`
//!   back: INDIRECT. (Keyed by shape it would stay INDIRECT: `seed_source`
//!   has `launch`'s zero-argument shape.)
//! * `back` turns the laundered integer back into a `fn()` and calls it at
//!   `launch`'s own shape: INDIRECT.
//! * `reshaped` transmutes `launch` to `fn(u8)`: the reification is refused
//!   (ESCAPES).
//! * `typed` makes the pointer with no LAUNDER.

#![allow(dead_code)]

fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

fn seed_source() -> u64 { 7 }

#[cfg(any(laundered, handed))]
pub fn entropy() -> usize { seed_source as usize }

#[cfg(any(laundered, handed))]
pub fn keep() -> fn() { launch } //[laundered,handed]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

#[cfg(handed)]
extern "C" {
    fn c_call_back(n: usize);
}

#[cfg(handed)]
pub fn hand(n: usize) { //[handed]~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}

#[cfg(back)]
pub fn stash() -> usize { launch as fn() as usize } //[back]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

#[cfg(back)]
pub fn unstash(u: usize) { //[back]~ NOTE may spawn (indirect)
    let f: fn() = unsafe { std::mem::transmute(u) };
    f()
}

#[cfg(reshaped)]
pub fn reshape() -> fn(u8) { unsafe { std::mem::transmute::<fn(), fn(u8)>(launch) } } //[reshaped]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

#[cfg(typed)]
pub fn keep() -> fn() { launch } //[typed]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

pub fn call_u8(f: fn(u8)) { f(1) }
