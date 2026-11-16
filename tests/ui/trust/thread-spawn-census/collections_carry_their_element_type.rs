//@ revisions: vec vec_deque hash_map plain
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[plain] forbid-output:may spawn (indirect): an indirect call
//@[plain] forbid-output:may spawn (indirect): the callee
//! Spawn census: `Vec<T>`, `VecDeque<T>` and the hash tables keep their
//! elements behind a `u8` pointer; the element type is only in a
//! `PhantomData<T>`, which rule H read as nothing. A collection of fn pointers
//! handed to C was plain data, so `hand` and the later `run` were QUIET though
//! C could call `launch` from it. A `PhantomData<T>` now carries what a `T`
//! carries: `hand` and `run` are INDIRECT. `plain` (a `Vec<u64>`) stays QUIET.

#![allow(dead_code, improper_ctypes)]

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(vec)]
type Callbacks = Vec<fn()>;
#[cfg(vec_deque)]
type Callbacks = std::collections::VecDeque<fn()>;
#[cfg(hash_map)]
type Callbacks = std::collections::HashMap<u32, fn()>;
#[cfg(plain)]
type Callbacks = Vec<u64>;

#[cfg(not(plain))]
pub fn make(callbacks: &mut Callbacks) {
    #[cfg(vec)]
    callbacks.push(launch);
    #[cfg(vec_deque)]
    callbacks.push_back(launch);
    #[cfg(hash_map)]
    callbacks.insert(0, launch);
}

unsafe extern "C" {
    fn c_take(callbacks: *const Callbacks);
    safe fn c_run();
}

pub fn hand(callbacks: &Callbacks) { //[vec,vec_deque,hash_map]~ NOTE may spawn (indirect)
    unsafe { c_take(callbacks) }
}

pub fn run() { //[vec,vec_deque,hash_map]~ NOTE may spawn (indirect)
    c_run()
}
