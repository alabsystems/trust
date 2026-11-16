//@ revisions: pointee union reference read transmute_copy bytes copy raw_parts positional
//@ revisions: signature static_bytes exposed hash_addr fn_addr static_ptr static_ref_static
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census, typed LAUNDER (design §10; KNOWN_HAZARDS "THE SPAWN CENSUS
//! SEES NO PUN"): every route by which a callable's bytes reach plain data is
//! a LAUNDER keyed by the callables those bytes may hold. The crate has no
//! value LAUNDER (no `f as usize`), so before typed LAUNDERs data held no
//! callable and `hand` was QUIET in every revision, though C calls `launch`
//! out of the integer it is handed. `keep` reads `launch`'s fn pointer as an
//! integer:
//!
//! * `pointee`: through a pointer to it cast to `*const usize` (route P, the
//!   P2m follow-up's probe l3);
//! * `union`: through a union field (route U);
//! * `reference`: through a transmute of `&fn()` to `&usize` (P);
//! * `read`: `ptr::read` of a cast pointer (P);
//! * `transmute_copy`: the cast is in core's generic body, walked at this
//!   instance (P);
//! * `bytes`: its bytes through a `*const u8` (P);
//! * `copy`: `ptr::copy_nonoverlapping` of its bytes into an integer (P);
//! * `raw_parts`: `ptr::from_raw_parts`, a pointer re-viewed with no cast (P);
//! * `positional`: a transmute that keeps every fn shape but moves the fn
//!   pointer's bytes onto data (a value LAUNDER, route V);
//! * `signature`: a fn pointer reshaped to take `&fn()` where its body reads
//!   `&usize` (route S);
//! * `static_bytes`: a static whose bytes hold the fn pointer at a
//!   `MaybeUninit<u8>` position (route C);
//! * `exposed`: the exposed address of a static holding it, which C may
//!   re-enter (route A, SC-7b).
//! * `hash_addr`: no unsafe code: hashing the fn pointer hands its code
//!   address to a `Hasher` (`impl<F: FnPtr> Hash for F`, through
//!   `FnPtr::addr`'s shim, route V);
//! * `fn_addr`: `FnPtr::addr` called directly (V);
//! * `static_ptr`: a static's pointer to another static holding it, cast to
//!   `*const usize` in the initializer: the target static's bytes are read
//!   again at the pointer's type (route C);
//! * `static_ref_static`: the same through a static reference to the bytes
//!   as `[MaybeUninit<u8>; N]` (C).
//!
//! `hand` gives the integer to C, which may call it back, and `launch`
//! spawns: `hand` is INDIRECT in every revision.

#![allow(dead_code)]
#![cfg_attr(raw_parts, feature(ptr_metadata))]
// Upstream 1.101: the `FnPtr` trait's feature is `fn_static` (was `fn_ptr_trait`).
#![cfg_attr(fn_addr, feature(fn_static))]

#[cfg(bytes)]
use std::convert::TryInto;
#[cfg(hash_addr)]
use std::hash::{Hash, Hasher};
#[cfg(fn_addr)]
// Upstream 1.101: the `FnPtr` trait moved from `std::marker` to `std::ops`.
use std::ops::FnPtr;
#[cfg(any(static_bytes, static_ref_static))]
use std::mem::MaybeUninit;

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(union)]
union Pun {
    f: fn(),
    n: usize,
}

#[cfg(positional)]
#[repr(C)]
struct FnFirst(fn(), usize);

#[cfg(positional)]
#[repr(C)]
struct DataFirst(usize, fn());

#[cfg(signature)]
fn read(p: &usize) -> usize {
    *p
}

#[cfg(static_bytes)]
static BYTES: [MaybeUninit<u8>; size_of::<fn()>()] =
    unsafe { std::mem::transmute::<fn(), _>(launch as fn()) };

#[cfg(exposed)]
static F: fn() = launch;

#[cfg(hash_addr)]
struct Grab(usize);

#[cfg(hash_addr)]
impl Hasher for Grab {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
    fn write_usize(&mut self, n: usize) {
        self.0 = n
    }
}

#[cfg(any(static_ptr, static_ref_static))]
static FN: fn() = launch;

#[cfg(static_ptr)]
struct Ptr(*const usize);

#[cfg(static_ptr)]
unsafe impl Sync for Ptr {}

#[cfg(static_ptr)]
static PTR: Ptr = Ptr(&FN as *const fn() as *const usize);

#[cfg(static_ref_static)]
static FN_BYTES: &[MaybeUninit<u8>; size_of::<fn()>()] =
    unsafe { &*(&FN as *const fn() as *const [MaybeUninit<u8>; size_of::<fn()>()]) };

#[cfg(not(any(positional, static_bytes, exposed, static_ptr, static_ref_static)))]
pub fn keep() -> usize {
    let f: fn() = launch;
    #[cfg(pointee)]
    let n = unsafe { *(&f as *const fn() as *const usize) };
    #[cfg(union)]
    let n = unsafe { Pun { f }.n };
    #[cfg(reference)]
    let n = unsafe { *std::mem::transmute::<&fn(), &usize>(&f) };
    #[cfg(read)]
    let n = unsafe { std::ptr::read(&f as *const fn() as *const usize) };
    #[cfg(transmute_copy)]
    let n = unsafe { std::mem::transmute_copy::<fn(), usize>(&f) };
    #[cfg(bytes)]
    let n = usize::from_ne_bytes(
        unsafe { std::slice::from_raw_parts(&f as *const fn() as *const u8, size_of::<usize>()) }
            .try_into()
            .unwrap(),
    );
    #[cfg(copy)]
    let n = {
        let mut n = 0usize;
        unsafe {
            std::ptr::copy_nonoverlapping(
                &f as *const fn() as *const u8,
                &mut n as *mut usize as *mut u8,
                size_of::<usize>(),
            )
        };
        n
    };
    #[cfg(raw_parts)]
    let n = unsafe { *std::ptr::from_raw_parts::<usize>(&f as *const fn(), ()) };
    #[cfg(signature)]
    let n = unsafe {
        std::mem::transmute::<fn(&usize) -> usize, fn(&fn()) -> usize>(read)(&f)
    };
    #[cfg(hash_addr)]
    let n = {
        let mut grab = Grab(0);
        f.hash(&mut grab);
        grab.0
    };
    // Upstream 1.101: `FnPtr::addr` returns the `usize` itself (was a raw
    // pointer whose `.addr()` the second call read).
    #[cfg(fn_addr)]
    let n = f.addr();
    n
}

#[cfg(positional)]
pub fn keep() -> usize {
    let data: DataFirst = unsafe { std::mem::transmute(FnFirst(launch, 0)) };
    data.0
}

#[cfg(static_bytes)]
pub fn keep() -> usize {
    unsafe { *(BYTES.as_ptr() as *const usize) }
}

#[cfg(exposed)]
pub fn keep() -> usize {
    &F as *const fn() as usize
}

#[cfg(static_ptr)]
pub fn keep() -> usize {
    unsafe { *PTR.0 }
}

#[cfg(static_ref_static)]
pub fn keep() -> usize {
    usize::from_ne_bytes(FN_BYTES.map(|byte| unsafe { byte.assume_init() }))
}

pub fn hand(n: usize) { //~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
