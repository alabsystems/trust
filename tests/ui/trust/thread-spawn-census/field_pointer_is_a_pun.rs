//@ revisions: raw raw_from_raw slice reference zst union_zst union_cvoid drop_glue
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Spawn census, typed LAUNDER route F (design §10; DECISION_QUEUE SC-7i): a
//! pointer to a field is a pointer to its base's memory at the field's type.
//! It changes the pointee type with no cast, so pointer arithmetic from it,
//! or a later cast of a field with no bytes, reads the base's other fields
//! at another type: here `launch`'s fn pointer as an integer.
//!
//! * `raw`: `(&raw const s.n).add(1).read()`;
//! * `raw_from_raw`: the same from a raw pointer to the struct, which keeps
//!   its provenance over all of it under every aliasing model;
//! * `slice`: `slice::from_raw_parts(&raw const s.n, 2)[1]`;
//! * `reference`: from `&s.n` (Stacked Borrows rejects the access, Tree
//!   Borrows allows it: the census takes the second, SC-7i);
//! * `zst`: a `()` field's pointer cast to `*const usize`;
//! * `union_zst`, `union_cvoid`: a union field of no bytes, or of `c_void`s,
//!   cast to `*const usize`;
//! * `drop_glue`: drop glue hands a field's `Drop` a reference to it, from
//!   which it reads the next field.
//!
//! The crate has no value LAUNDER, `hand` gives the integer to C, which may
//! call it back, and `launch` spawns: `hand` is INDIRECT in every revision.

#![allow(dead_code)]

extern "C" {
    fn c_call_back(n: usize);
}

fn launch() {
    let _handle = std::thread::spawn(|| {});
}

#[cfg(any(raw, raw_from_raw, slice, reference))]
#[repr(C)]
struct NumberFirst {
    n: usize,
    f: fn(),
}

#[cfg(zst)]
#[repr(C)]
struct UnitFirst {
    unit: (),
    f: fn(),
}

#[cfg(union_zst)]
union UnitOrFn {
    f: fn(),
    unit: (),
}

#[cfg(union_cvoid)]
union VoidsOrFn {
    f: fn(),
    voids: std::mem::ManuallyDrop<[std::ffi::c_void; size_of::<fn()>()]>,
}

#[cfg(drop_glue)]
static SEEN: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[cfg(drop_glue)]
struct Peek(usize);

#[cfg(drop_glue)]
impl Drop for Peek {
    fn drop(&mut self) {
        let next = unsafe { (self as *mut Peek).add(1).cast::<usize>().read() };
        SEEN.store(next, std::sync::atomic::Ordering::Relaxed);
    }
}

#[cfg(drop_glue)]
#[repr(C)]
struct PeekFirst {
    peek: Peek,
    f: fn(),
}

pub fn keep() -> usize {
    #[cfg(any(raw, raw_from_raw, slice, reference))]
    let s = NumberFirst { n: 0, f: launch };
    #[cfg(raw)]
    let n = unsafe { (&raw const s.n).add(1).read() };
    #[cfg(raw_from_raw)]
    let n = {
        let p: *const NumberFirst = &raw const s;
        unsafe { (&raw const (*p).n).add(1).read() }
    };
    #[cfg(slice)]
    let n = unsafe { std::slice::from_raw_parts(&raw const s.n, 2)[1] };
    #[cfg(reference)]
    let n = unsafe { (&s.n as *const usize).add(1).read() };
    #[cfg(zst)]
    let n = {
        let s = UnitFirst { unit: (), f: launch };
        unsafe { (&raw const s.unit as *const usize).read() }
    };
    #[cfg(union_zst)]
    let n = {
        let u = UnitOrFn { f: launch };
        unsafe { (&raw const u.unit as *const usize).read() }
    };
    #[cfg(union_cvoid)]
    let n = {
        let u = VoidsOrFn { f: launch };
        unsafe { (&raw const u.voids as *const usize).read() }
    };
    #[cfg(drop_glue)]
    let n = {
        drop(PeekFirst { peek: Peek(0), f: launch });
        SEEN.load(std::sync::atomic::Ordering::Relaxed)
    };
    n
}

pub fn hand(n: usize) { //~ NOTE may spawn (indirect)
    unsafe { c_call_back(n) }
}
