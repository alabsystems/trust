//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-ARF): a THIN RAW-POINTER field of a struct literal is admissible
//! when its pointer STRICTLY OUTLIVES the call — and only then.
//!
//! The address vocabulary was already shipped bare (`&raw mut STATIC` lowers to
//! `GlobalAddr` and joins `borrow_ptrs` + `global_ptrs`); the refusal was purely
//! that the admissibility predicate's only accepting arm spelled `ty::Ref`.
//!
//! The asymmetry with the `&T` arm is the whole soundness argument: the ref arm
//! also admits the NAMED-FRAME half (a `&local` snapshot, a promoted slot),
//! because borrowck rejects returning an aggregate that holds one. A raw
//! pointer has no such backstop, so the raw arm takes the outlives half ALONE.

pub static mut STATIC: u32 = 42;

pub struct SyncPtr {
    pub foo: *mut u32,
}
unsafe impl Sync for SyncPtr {}

pub static PTR: SyncPtr = SyncPtr { foo: &raw mut STATIC };

fn main() {
    unsafe {
        assert_eq!(*PTR.foo, 42);
        *PTR.foo = 7;
        assert_eq!(STATIC, 7);
    }
}
