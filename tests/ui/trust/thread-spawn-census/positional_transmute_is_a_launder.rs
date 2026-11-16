//@ revisions: swapped fn_only
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[fn_only] forbid-output:may spawn (indirect): an indirect call
//@[fn_only] forbid-output:may spawn (indirect): the callee
//! Spawn census: a value reinterpretation LAUNDERs when it moves a fn
//! pointer's bytes onto data. Fn shapes were compared as sets, so `(fn(),
//! usize)` read as `(usize, fn())` kept every shape and recorded nothing:
//! with no LAUNDER anywhere, the integer handed to C was plain data and `hand`
//! was QUIET though it held `launch`. The census reads no layout, so a target
//! holding data beside the source's fn pointers now launders (`swapped`:
//! `hand` is INDIRECT). A reshape onto fn pointers alone is no LAUNDER
//! (`fn_only`: QUIET).

#![allow(dead_code)]

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[repr(C)]
struct Pair {
    f: fn(),
    n: usize,
}

#[cfg(swapped)]
#[repr(C)]
struct Swapped {
    n: usize,
    f: fn(),
}

#[cfg(swapped)]
pub fn keep() -> usize {
    let pair = Pair { f: launch, n: 0 };
    let swapped: Swapped = unsafe { std::mem::transmute(pair) };
    swapped.n
}

#[cfg(fn_only)]
pub fn keep() -> fn() {
    let both: (fn(), fn()) = (launch, launch);
    let array: [fn(); 2] = unsafe { std::mem::transmute(both) };
    array[1]
}

unsafe extern "C" {
    safe fn c_call_back(n: usize);
}

pub fn hand(n: usize) { //[swapped]~ NOTE may spawn (indirect)
    c_call_back(n)
}
