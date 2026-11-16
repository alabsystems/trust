//@ needs-trust-verify
//@ aux-build: std_member_withheld_dep.rs
//@ aux-build: sysroot_drop_reach_dep.rs
//@ revisions: ioerror_drop_strict ioerror_drop_default ioerror_drop_certify
//@ revisions: ioerror_scope_strict ioerror_scope_default ioerror_scope_certify
//@ revisions: waker_drop_strict waker_drop_default waker_drop_certify
//@ revisions: ioerror_result_certify
//@ revisions: waker_option_certify waker_tuple_certify waker_closure_certify localwaker_certify
//@ revisions: rc_dyn_any_strict rc_dyn_any_certify arc_dyn_error_certify rc_dyn_fn_certify
//@ revisions: rc_dep_bomb_certify arc_dep_bomb_certify cell_set_rc_dyn_certify
//@ revisions: cell_set_rc_dyn_nobundle_certify
//@ revisions: box_dep_alloc_certify rc_dep_alloc_certify
//@ revisions: box_dyn_error_strict box_dyn_error_certify ioerror_from_kind_certify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[ioerror_drop_strict] compile-flags: -Ztrust-policy=strict
//@[ioerror_scope_strict] compile-flags: -Ztrust-policy=strict
//@[waker_drop_strict] compile-flags: -Ztrust-policy=strict
//@[rc_dyn_any_strict] compile-flags: -Ztrust-policy=strict
//@[box_dyn_error_strict] compile-flags: -Ztrust-policy=strict
//@[ioerror_drop_certify] compile-flags: -Ztrust-policy=certify
//@[ioerror_scope_certify] compile-flags: -Ztrust-policy=certify
//@[waker_drop_certify] compile-flags: -Ztrust-policy=certify
//@[ioerror_result_certify] compile-flags: -Ztrust-policy=certify
//@[waker_option_certify] compile-flags: -Ztrust-policy=certify
//@[waker_tuple_certify] compile-flags: -Ztrust-policy=certify
//@[waker_closure_certify] compile-flags: -Ztrust-policy=certify
//@[localwaker_certify] compile-flags: -Ztrust-policy=certify
//@[rc_dyn_any_certify] compile-flags: -Ztrust-policy=certify
//@[arc_dyn_error_certify] compile-flags: -Ztrust-policy=certify
//@[rc_dyn_fn_certify] compile-flags: -Ztrust-policy=certify
//@[rc_dep_bomb_certify] compile-flags: -Ztrust-policy=certify
//@[arc_dep_bomb_certify] compile-flags: -Ztrust-policy=certify
//@[cell_set_rc_dyn_certify] compile-flags: -Ztrust-policy=certify
//@[cell_set_rc_dyn_nobundle_certify] compile-flags: -Ztrust-policy=certify
//@[cell_set_rc_dyn_nobundle_certify] rustc-env:TRUST_NO_BUNDLE_STD=1
//@[box_dep_alloc_certify] compile-flags: -Ztrust-policy=certify
//@[rc_dep_alloc_certify] compile-flags: -Ztrust-policy=certify
//@[box_dyn_error_certify] compile-flags: -Ztrust-policy=certify
//@[ioerror_from_kind_certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! A sysroot type's drop glue may be credited as the sysroot's own code only
//! when it CANNOT reach code outside the sysroot (2026-09-29).
//!
//! Sysroot drop glue is credited by belief — an admitted sysroot destructor
//! (`admit_foreign_destructor`) and the bridge's name-keyed std arms
//! (`is_std_owning_or_scaffold`, …) both lower the drop to `Assert(true)`. That
//! belief is the sysroot TCB, a claim about core/alloc/std's own code. It says
//! nothing about the code a dropped VALUE hands the sysroot to run: a function
//! pointer stored in it (`Waker`'s `RawWakerVTable::drop`; `io::Error`'s
//! `Custom`/`CustomOwner` droppers, which drop a `Box<dyn Error>`), a `dyn`
//! pointee (`Rc<dyn Any>`, whose descent in the bridge stops at the `NonNull`
//! field because a `NonNull` drops nothing), a dependency type owned through an
//! erased pointer (`Rc<dep::Bomb>`), or a dependency allocator
//! (`Box<u32, dep::DepAlloc>`). Now each ADT a body drops or hands to a generic
//! callee is asked, on its concrete rustc type, whether its drop glue can reach
//! such code (`trust_verify/sysroot_drop_reach.rs`), and the bridge credits no
//! node that can, by any arm.
//!
//! BEFORE (stage 1 of origin/main `fbb9fa383d2`, m3's debug std, measured
//! 2026-09-29): every revision below except the three control revisions at the
//! end built exit 0 under its policy, `certify` included, with
//! `functions_verified` 1 of 1 (`waker_closure`: 2 of 2). For every shape but
//! `localwaker` (not run), a probe of the same shape built verify-off and called
//! from a verify-off `main` with the dependency's value (`drop_err(7)`,
//! `waker(7)`, `Rc::new(Bomb(7))`, a `DepAlloc(7)` box, …) panicked in the
//! dependency (exit 101). AFTER: each is refused, the row naming the drop glue
//! whose credit was withdrawn, and `p` is not counted verified.
//!
//! Controls that STAY refused, unchanged: `box_dyn_error` (a `Box<dyn Error>`
//! drop, refused before this change on the bridge's own `dyn` arm) and
//! `ioerror_from_kind` (an `io::Error` built from an `ErrorKind`, which runs no
//! dependency code at run time but is refused on origin/main as well; this change
//! cannot tell the tag of an `io::Error` apart, so it could not admit it either).
//! Its row depends on the std build: a debug std refuses the call to
//! `Repr::new_simple` (its `debug_assert!`) as an absent callee, while a release std
//! lowers that call and refuses the `io::Error` drop glue. So it pins only the
//! refusal and that `p` is not verified.
//! The credit this change must KEEP is pinned by
//! `sysroot_drop_reach_keeps_sysroot_credit.rs`.
#![cfg_attr(any(box_dep_alloc_certify, rc_dep_alloc_certify), feature(allocator_api))]
#![cfg_attr(localwaker_certify, feature(local_waker))]

// The values a caller passes: `dep::drop_err`, `dep::waker`, `rdep::Bomb`,
// `rdep::DepAlloc`.
extern crate std_member_withheld_dep as dep;
extern crate sysroot_drop_reach_dep as rdep;

pub enum Tag {
    A,
    B,
}

// The prior LEAD's three shapes, each under strict, the default policy and certify.

#[cfg(any(ioerror_drop_strict, ioerror_drop_default, ioerror_drop_certify))]
pub fn p(t: Tag, e: std::io::Error) -> usize {
    let c = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if c == 7 {
        return c;
    }
    drop(e);
    c
}

#[cfg(any(ioerror_scope_strict, ioerror_scope_default, ioerror_scope_certify))]
pub fn p(t: Tag, e: std::io::Error) -> usize {
    let c = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if c == 7 {
        return c;
    }
    let _keep = e;
    c
}

#[cfg(any(waker_drop_strict, waker_drop_default, waker_drop_certify))]
pub fn p(t: Tag, w: std::task::Waker) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if b == 7 {
        return b;
    }
    drop(w);
    b
}

// The same reach, through other owners and shapes.

#[cfg(ioerror_result_certify)]
pub fn p(r: std::io::Result<u32>) -> u32 {
    match r {
        Ok(v) => v / 2,
        Err(_) => 0,
    }
}

#[cfg(waker_option_certify)]
pub fn p(t: Tag, w: Option<std::task::Waker>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(w);
    b
}

#[cfg(waker_tuple_certify)]
pub fn p(t: Tag, w: (u8, std::task::Waker)) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(w);
    b
}

#[cfg(waker_closure_certify)]
pub fn p(t: Tag, w: std::task::Waker) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    let f = move || {
        let _ = &w;
        1u32
    };
    drop(f);
    b
}

#[cfg(localwaker_certify)]
pub fn p(t: Tag, w: std::task::LocalWaker) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(w);
    b
}

#[cfg(any(rc_dyn_any_strict, rc_dyn_any_certify))]
pub fn p(t: Tag, r: std::rc::Rc<dyn std::any::Any>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(r);
    b
}

#[cfg(arc_dyn_error_certify)]
pub fn p(t: Tag, r: std::sync::Arc<dyn std::error::Error + Send + Sync>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(r);
    b
}

#[cfg(rc_dyn_fn_certify)]
pub fn p(t: Tag, r: std::rc::Rc<dyn Fn() -> u8>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(r);
    b
}

#[cfg(rc_dep_bomb_certify)]
pub fn p(t: Tag, r: std::rc::Rc<rdep::Bomb>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(r);
    b
}

#[cfg(arc_dep_bomb_certify)]
pub fn p(t: Tag, r: std::sync::Arc<rdep::Bomb>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(r);
    b
}

// `Cell::set` drops the old value inside core, with no `Drop` terminator in `p`.
// `_nobundle` keeps `Cell::set` out of the bundle (`TRUST_NO_BUNDLE_STD=1`), so the
// only body the reach scan sees is `p`'s: it must ask the call's generic ARGUMENT
// (`Option<Rc<dyn Any>>`), not a dropped type. Without that root the revision built
// exit 0 under certify (0 verified, one unknown row) and the program panicked
// (measured by mutation, 2026-09-29).
#[cfg(any(cell_set_rc_dyn_certify, cell_set_rc_dyn_nobundle_certify))]
pub fn p(t: Tag, cell: &std::cell::Cell<Option<std::rc::Rc<dyn std::any::Any>>>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    cell.set(None);
    b
}

#[cfg(box_dep_alloc_certify)]
pub fn p(t: Tag, v: Box<u32, rdep::DepAlloc>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(v);
    b
}

#[cfg(rc_dep_alloc_certify)]
pub fn p(t: Tag, v: std::rc::Rc<u32, rdep::DepAlloc>) -> u32 {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(v);
    b
}

// Controls: refused before this change, and still.

#[cfg(any(box_dyn_error_strict, box_dyn_error_certify))]
pub fn p(t: Tag, e: Box<dyn std::error::Error + Send + Sync>) -> usize {
    let c = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if c == 7 {
        return c;
    }
    drop(e);
    c
}

#[cfg(ioerror_from_kind_certify)]
pub fn p(t: Tag) -> usize {
    let e = std::io::Error::from(std::io::ErrorKind::Other);
    let c = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    drop(e);
    c
}

//[ioerror_drop_strict,ioerror_drop_default,ioerror_drop_certify]~? RAW drop glue for `core::io::error::Error` has unproven panic-freedom
//[ioerror_scope_strict,ioerror_scope_default,ioerror_scope_certify]~? RAW drop glue for `core::io::error::Error` has unproven panic-freedom
//[waker_drop_strict,waker_drop_default,waker_drop_certify]~? RAW drop glue for `core::task::wake::Waker` has unproven panic-freedom
//[ioerror_result_certify]~? RAW drop glue for variant `Err` (#1) of
//[cell_set_rc_dyn_certify]~? RAW drop glue for variant `Some` (#1) of
// CALL-REACH-1 D7 (2026-10-13, DECISION_QUEUE CALL-REACH-1-D7): the waker `p` drops is a
// PARAMETER, so `drop(w)` hands `mem::drop` a value holding a `RawWakerVTable` the body did not
// build; the call walk opens at the vtable's `drop` pointer and the bridge withdraws the bundled
// `mem::drop` call itself. The refusal is that withdrawn call's row, not the member's drop glue.
//[waker_option_certify]~? RAW `core::mem::drop::<core::option::Option<core::task::wake::Waker>>` is a std/core/alloc function
//[waker_tuple_certify]~? RAW `core::mem::drop::<(u8, core::task::wake::Waker)>` is a std/core/alloc function
//[waker_closure_certify]~? RAW `core::mem::drop::<{closure@
//[localwaker_certify]~? RAW `core::mem::drop::<core::task::wake::LocalWaker>` is a std/core/alloc function
//[rc_dyn_any_strict,rc_dyn_any_certify,rc_dyn_fn_certify,rc_dep_bomb_certify,rc_dep_alloc_certify]~? RAW drop glue for `alloc::rc::Rc` has unproven panic-freedom
//[arc_dyn_error_certify,arc_dep_bomb_certify]~? RAW drop glue for `alloc::sync::Arc` has unproven panic-freedom
//[box_dep_alloc_certify,box_dyn_error_strict,box_dyn_error_certify]~? RAW drop glue for `alloc::boxed::Box` has unproven panic-freedom
//[ioerror_from_kind_certify]~? RAW "functions_verified":0,
//[waker_closure_certify]~? RAW "functions_verified":1,
//[ioerror_drop_strict,ioerror_drop_default,ioerror_drop_certify]~? RAW "functions_verified":0,
//[ioerror_scope_strict,ioerror_scope_default,ioerror_scope_certify]~? RAW "functions_verified":0,
//[waker_drop_strict,waker_drop_default,waker_drop_certify]~? RAW "functions_verified":0,
//[ioerror_result_certify,waker_option_certify,waker_tuple_certify,localwaker_certify]~? RAW "functions_verified":0,
//[rc_dyn_any_strict,rc_dyn_any_certify,arc_dyn_error_certify,rc_dyn_fn_certify]~? RAW "functions_verified":0,
//[rc_dep_bomb_certify,arc_dep_bomb_certify,cell_set_rc_dyn_certify]~? RAW "functions_verified":0,
//[box_dep_alloc_certify,rc_dep_alloc_certify]~? RAW "functions_verified":0,
//[cell_set_rc_dyn_nobundle_certify]~? RAW "functions_verified":0,
