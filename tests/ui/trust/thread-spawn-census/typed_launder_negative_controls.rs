//@ revisions: fmt boxdyn cast_data typed_vec swap maybeuninit lazylock lazylock_bytes catch_unwind
//@ revisions: confined scope catch_spawn
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[fmt] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[boxdyn] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[cast_data] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[typed_vec] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[swap] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[maybeuninit] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[lazylock_bytes] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[catch_unwind] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[confined] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[scope] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@[catch_spawn] rustc-env:TRUST_SPAWN_CENSUS_DEBUG=1
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[fmt] forbid-output:): hand -
//@[boxdyn] forbid-output:): hand -
//@[cast_data] forbid-output:): hand -
//@[typed_vec] forbid-output:): hand -
//@[swap] forbid-output:): hand -
//@[maybeuninit] forbid-output:): hand -
//@[lazylock_bytes] forbid-output:): hand -
//@[catch_unwind] forbid-output:): hand -
//@[confined] forbid-output:): hand -
//@[confined] forbid-output:may spawn (indirect): an indirect call
//@[confined] forbid-output:may spawn (indirect): the callee
//@[scope] forbid-output:): hand -
//@[catch_spawn] forbid-output:): hand -
//! Spawn census, typed LAUNDER (design §10): what must NOT put a spawning
//! callable into plain data. `launch` (`fn()`) spawns, `keep` makes it a fn
//! pointer, and `hand` gives an integer to C, which may call it back; the
//! crate has no value LAUNDER, so `hand` is refused exactly when some
//! reinterpretation put a zero-argument fn into data. Each revision adds
//! benign code that reinterprets memory but puts none there, so no
//! candidate row starts at `hand` (the census's `TRUST_SPAWN_CENSUS_DEBUG`
//! rows, `<span>: hand -<class>-> …`). Other functions may still be refused
//! through rule H paths older than the typed LAUNDER: `format!` hands
//! `fmt::Arguments` (an untyped `NonNull<()>`) to code that may call any
//! callable, a `&OnceLock` carries the queue `Once`'s `AtomicPtr<()>`, and a
//! `fn()` handed to a callee that can panic may be called; `keep` makes
//! `launch` a member every one of those reaches.
//!
//! * `fmt`: formatting erases each argument to `NonNull<()>` and reshapes its
//!   formatter, and `Arguments::as_str` reads a pointer as an integer; the
//!   erased values are integers and strings, and an address read as data
//!   launders nothing behind it (SC-7b).
//! * `boxdyn`: freeing a `Box<dyn Any>` and a `Box<dyn Error>` views each
//!   object's bytes as `u8`: a `u32` and a `String` hold no callable, and a
//!   vtable word is none in data (SC-7c).
//! * `cast_data`: `&[u32]` read as bytes.
//! * `typed_vec`: a `Vec<u64>` and a `HashMap<u32, String>` (their buffers'
//!   `u8` views hold no callable).
//! * `swap`: `mem::swap` of integer arrays (byte chunks).
//! * `maybeuninit`: a `MaybeUninit<fn()>` (SC-7d: core's own union).
//! * `lazylock_bytes`: a static `LazyLock<u32>`, whose `Data` union holds a
//!   `fn() -> u32` (a closure's `call_once` shim) in the static's bytes, read
//!   but never forced: those bytes are typed by the union's fields (SC-7d:
//!   std's own union, guarded by its `Once`), so route C records nothing.
//! * `lazylock` (REFUSED, the measured cost of SC-7e): the same static,
//!   forced. Its `Data` fields, which std projects, are no pun site (SC-7d),
//!   but `force` takes the `fn() -> u32` out with `ptr::read`, whose
//!   `ub_checks` precondition erases the pointer to `*const ()`, a view that
//!   keeps no position: the zero-argument shape IS in data and `hand` is
//!   refused. Recognizing address-only erasures (DECISION_QUEUE SC-7e, not
//!   built) would make it QUIET; this revision shows when it does. (No
//!   census debug output here: the refused `hand`'s candidate rows overflow
//!   the test's captured output.)
//! * `catch_unwind`: std's `Data` union of the closure and its result
//!   (SC-7d).
//! * `confined`: `confined_dyn_erasure.rs`'s `once` and `map` (a spawning
//!   initializer and a spawning `Hash`, each a confined `dyn` value) with a
//!   pun of an unrelated `fn(u8)`, and no `keep`: a LAUNDER of fn keys demotes
//!   no confined member, so `name` and `quiet` stay QUIET and no row of the
//!   crate is INDIRECT (any LAUNDER used to demote every confined member,
//!   which std's `Once::call` and hashbrown's rehash then reach).
//! * `scope`, `catch_spawn`: a scoped thread, and `catch_unwind` of a
//!   spawning closure. std hands `catch_unwind` its `do_call::<F, R>` reified
//!   to a `fn(*mut u8)`, a common shape std's own puns put into data; the
//!   intrinsic only calls it, which the census charges as a RUN of the item,
//!   so it is no FnPool member (SC-7h) and data cannot hold it.

#![allow(dead_code)]

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(not(confined))]
pub fn keep() -> fn() {
    launch
}

pub fn hand(n: usize) { //[lazylock]~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}

#[cfg(fmt)]
pub fn benign(n: u32) -> (String, Option<&'static str>) {
    (format!("{n} {}", "x"), format_args!("x").as_str())
}

#[cfg(boxdyn)]
pub fn benign() {
    drop(Box::new(5u32) as Box<dyn std::any::Any>);
    drop(Box::<dyn std::error::Error>::from("x"));
}

#[cfg(cast_data)]
pub fn benign(x: &[u32]) -> &[u8] {
    unsafe { std::slice::from_raw_parts(x.as_ptr() as *const u8, size_of_val(x)) }
}

#[cfg(typed_vec)]
pub fn benign() -> usize {
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    let mut m: std::collections::HashMap<u32, String> = std::collections::HashMap::new();
    m.insert(1, String::from("x"));
    v.len() + m.len()
}

#[cfg(swap)]
pub fn benign() -> u64 {
    let mut a = [0u64; 4];
    let mut b = [1u64; 4];
    std::mem::swap(&mut a, &mut b);
    a[0]
}

#[cfg(maybeuninit)]
pub fn benign() -> fn() {
    unsafe { std::mem::MaybeUninit::<fn()>::new(keep()).assume_init() }
}

#[cfg(any(lazylock, lazylock_bytes))]
static L: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| 1);

#[cfg(lazylock)]
pub fn benign() -> u32 {
    *L
}

#[cfg(lazylock_bytes)]
pub fn benign() -> &'static std::sync::LazyLock<u32> {
    &L
}

#[cfg(catch_unwind)]
pub fn benign() -> u32 {
    std::panic::catch_unwind(|| 1u32).unwrap_or(0)
}

#[cfg(scope)]
pub fn benign() {
    std::thread::scope(|s| {
        s.spawn(|| {});
    });
}

#[cfg(catch_spawn)]
pub fn benign() -> bool {
    std::panic::catch_unwind(|| launch()).is_ok()
}

#[cfg(confined)]
mod confined {
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};
    use std::sync::OnceLock;

    static CONNECTOR: OnceLock<u32> = OnceLock::new();
    static NAME: OnceLock<u32> = OnceLock::new();

    // A spawning initializer and a spawning `Hash`, each erased as a
    // confined `dyn` value of a std frame's local.
    pub fn start() -> u32 {
        *CONNECTOR.get_or_init(|| {
            let _handle = std::thread::spawn(|| {});
            1
        })
    }

    pub fn name() -> u32 {
        *NAME.get_or_init(|| 5)
    }

    #[derive(PartialEq, Eq)]
    pub struct Loud(pub u32);

    impl Hash for Loud {
        fn hash<H: Hasher>(&self, state: &mut H) {
            let _handle = std::thread::spawn(|| {});
            self.0.hash(state);
        }
    }

    pub fn loud(m: &mut HashMap<Loud, u32>) {
        m.insert(Loud(1), 1);
    }

    pub fn quiet(m: &mut HashMap<u32, u32>) {
        m.insert(1, 1);
    }

    fn seed(_: u8) {}

    pub fn pun() -> usize {
        let f: fn(u8) = seed;
        unsafe { *(&f as *const fn(u8) as *const usize) }
    }
}
