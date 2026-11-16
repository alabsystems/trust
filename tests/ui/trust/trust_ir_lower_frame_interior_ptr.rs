//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-FIL): the FRAME-INTERIOR LEDGER SPLIT — a +0-body soundness repair,
//! pinned by control fixtures because coverage cannot show it fired.
//!
//! `interior_ptrs` is documented as "the SUBSET of `borrow_ptrs` that are DERIVED
//! INTERIOR pointers ... the pointee is CALLER memory that provably outlives the
//! call", and it is one of only THREE classes the two return-escape guards except.
//! Two of its six writers pushed into it UNCONDITIONALLY, and for both the pointee
//! provably does NOT outlive the frame:
//!
//!   * `lower_field_of_local_addr` — its GEP base is `self.promoted_slot(var)`, and
//!     `promoted_slot` reads only `promoted_slots`, every member of which is an
//!     `Alloca` minted by `alloc_promoted`. A frame address, in the class that means
//!     "not a frame address".
//!   * `ledger_box_data_ptr` — a `Box<T>` data pointer, justified as "heap memory
//!     outliving the frame", which is FALSE for a Box this frame OWNS and therefore
//!     DROPS.
//!
//! The repair INHERITS THE BASE CLASS, the discipline the other three writers
//! (wave-25b, wave-DP, wave-L4G) already follow: `interior_ptrs` only when the base
//! is itself in `ref_param_ptrs`; otherwise `frame_interior_ptrs`, which is excepted
//! by no return guard. `global_ptrs` is deliberately NOT an inheritance source.
//! When this guard landed, assembly copied a Rust static per body (`q_set` wrote
//! `@global.1` while `q_get` read `@global.2` for the same `static mut Q`). The
//! shared-static-identity assembly repair preserves compiler identity across
//! bodies; its run-make regression is separate from this lifetime ledger.
//! Shared storage alone does not discharge the pointer's lifetime/aliasing
//! obligations, so that repair does not widen this return-escape exemption.
//!
//! IT IS NOT A MISCOMPILE AND NEVER WAS. Every body below returns a raw pointer to
//! dead memory in the SOURCE too — legal Rust, only the dereference is UB — and
//! rustc's own MIR returns the same address, which is why R1/R2/R3/R4 are `clean`
//! AND strict-GREEN before this wave. What was wrong is the CLAIM: a consumer
//! reading `interior_ptrs` as its doc licenses ("outlives the frame") concluded
//! something false about a returned pointer. The lane declined the exploitable
//! spellings only by an accident of what borrowck permits — `&(*p).b` peels to
//! `NotAPlace` and never reaches the site at all — so it was fail-OPEN, and any
//! widening of `reborrow_target`'s Field arm (a tuple base, a Deref base, a nested
//! base — exactly what the F2 coverage lanes want next) makes it reachable.
//!
//! THIS FILE IS THE ONLY INSTRUMENT THAT SEES THE CHANGE. Measured on the pinned
//! 2,000-file ui corpus (lv2-subject-0831, 6,010/7,257 clean): the frame-slot GEP
//! fires in 9 clean bodies and NONE of them returns the pointer, and the Box
//! aggregate path fires in 0. Corpus delta: +0 clean, -0 clean, exactly.
//!
//! Under `strict`, so a refusal is a compile error AND the MIR re-derived from the
//! producer's own trust-ir must still agree with the built MIR for every body that
//! keeps lowering. The tag is deliberately not asserted, only that the body refuses.

#![allow(dead_code)]

pub struct W {
    pub a: i32,
    pub b: i32,
}

pub struct P<'a> {
    pub p: &'a i32,
    pub n: i32,
}

pub struct Inner {
    pub v: i32,
    pub w: i32,
}

pub struct Outer {
    pub head: i32,
    pub inner: Inner,
}

// ---------------------------------------------------------------------------
// MUST REFUSE. Each was clean before wave-FIL; each returns an address this frame
// owns. Delete the base-class test and these four lines stop erroring — nothing
// else in the tree would say so.
// ---------------------------------------------------------------------------

// R1 — the shipped witness (report addendum 2). Shared borrow of a promoted
// local's field, returned as a raw pointer past the frame that owns it.
pub fn promoted_escape() -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let mut w = W { a: 1, b: 2 };
    let r = &mut w.b;
    *r = 5;
    &w.b as *const i32
}

// R2 — the SAME writer through the `&mut` arm, with the interior pointer itself
// (not a re-borrow of the field) as the tail. Pinned separately because the
// mutable arm also pushes `mut_borrow_ptrs`, which the repair must not disturb.
pub fn promoted_mut_escape() -> *mut i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let mut w = W { a: 1, b: 2 };
    let r = &mut w.b;
    *r = 5;
    r as *mut i32
}

// R3 — the Box AGGREGATE path: a `Box<T>` VALUE is owned by whoever holds it, and
// that is this frame, so `&*b` addresses a block this frame's drop glue frees.
pub fn boxwhole_raw() -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let b: Box<i32> = Box::new(7);
    &*b as *const i32
}

// R4 — the Box MEMORY path with a FRAME base: the negative side of the
// inheritance test. `r` is a snapshot of a LOCAL box, not a ref param, so the
// data pointer loaded through it is frame-interior. Its positive twin is K6.
pub fn box_local_via_ref() -> *const i32 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let b: Box<i32> = Box::new(1);
    let r = &b;
    &**r as *const i32
}

// ---------------------------------------------------------------------------
// MUST STAY CLEAN. If any of these starts erroring, the repair over-fired: it
// removed a capability instead of a claim.
// ---------------------------------------------------------------------------

// K1 — the ordinary IN-FRAME use of the very pointer R1 refuses to return. The
// GEP, the `Store` through it and the read-back are all still admitted; only the
// escape is gone.
pub fn promoted_inframe() -> i32 {
    let mut w = W { a: 1, b: 2 };
    let r = &mut w.b;
    *r = 9;
    w.a + w.b
}

// K2/K3 — the `borrow_ptr_field_admissible` controls, and the reason this repair
// costs zero coverage. That predicate is "outlives the call OR is a named frame
// place", and it already admits `promoted_slots` and `local_snapshot_ptrs`; the
// new ledger joins that second half, so a frame interior pointer may still be
// INSERTED as a thin `&T` aggregate field exactly as before. (A RAW-pointer field
// was never admitted — the predicate requires `ty::Ref` — so the escape this
// half could have laundered does not exist.)
pub fn frame_field_tuple_scalar() -> i32 {
    let mut w = W { a: 1, b: 2 };
    let r = &mut w.b;
    *r = 5;
    let t = (&w.b, 7i32);
    t.1
}

pub fn frame_field_struct_scalar() -> i32 {
    let mut w = W { a: 1, b: 2 };
    let r = &mut w.b;
    *r = 5;
    let s = P { p: &w.b, n: 9 };
    s.n
}

// K4 — wave-25b, the writer that was ALREADY correct by construction: the base is
// a ref PARAM, so the interior address is caller memory and returning it is
// faithful. `get_a` is the offset-0 tautology (no GEP at all), `get_b` the real
// flat-I8 GEP. These are the whole point of `interior_ptrs`; they must not move.
pub fn get_a(w: &W) -> &i32 {
    &w.a
}

pub fn get_b(w: &W) -> &i32 {
    &w.b
}

// K5/K6 — the Box MEMORY path with a REF-PARAM base: the positive side of the
// inheritance test. The caller owns and drops the Box, so its block outlives the
// call and `&**b` is returnable.
pub fn box_param_ref(b: &Box<i32>) -> &i32 {
    &**b
}

pub fn box_param_read(b: &Box<i32>) -> i32 {
    **b
}

pub fn box_mut_param(b: &mut Box<i32>) -> i32 {
    **b = 3;
    **b
}

// K7 — the Box AGGREGATE path where the data pointer is READ THROUGH rather than
// returned. `frame_interior_ptrs` keeps every non-escape consumer, so this is
// untouched by the split.
pub fn box_whole_read() -> i32 {
    let b: Box<i32> = Box::new(1);
    *b
}

// K8 — wave-DP, the other correct-by-construction writer: it gates on
// `ref_param_ptrs && is_mut_borrow_ptr` BEFORE its pushes, so the repair is a
// no-op here. Pinned so a future edit cannot quietly move the accessor lane onto
// the frame ledger.
impl core::ops::Deref for Outer {
    type Target = Inner;
    fn deref(&self) -> &Inner {
        &self.inner
    }
}

impl core::ops::DerefMut for Outer {
    fn deref_mut(&mut self) -> &mut Inner {
        &mut self.inner
    }
}
