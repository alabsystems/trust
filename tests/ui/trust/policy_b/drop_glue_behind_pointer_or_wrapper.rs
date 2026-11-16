//@ needs-trust-verify
//@ edition: 2021
//@ no-prefer-dynamic
//@ aux-build:dropglue_bomb_dep.rs
//@ aux-build:panicking_allocator_dep.rs
//@ revisions: total rc arc opt_rc arr_iter local_struct closure rc_alloc arc_alloc thin_box waker mpmc_rx enum_rewrite
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[total] check-pass
//@[rc] check-fail
//@[arc] check-fail
//@[opt_rc] check-fail
//@[arr_iter] check-fail
//@[local_struct] check-fail
//@[closure] check-fail
//@[rc_alloc] check-fail
//@[arc_alloc] check-fail
//@[thin_box] check-fail
//@[waker] check-fail
//@[mpmc_rx] check-fail
//@[enum_rewrite] check-fail
//! The bridge's drop classifier must reach an element dropped THROUGH a pointer or a
//! never-drops wrapper (2026-10-08, review round 72). Each of the six failing revisions
//! drops a `dropglue_bomb_dep::Bomb`, whose verify-off `Drop` panics, and each was
//! PROVED under the default policy and `certify` before the fix:
//!  * `Rc`/`Arc` walk `NonNull<RcInner<T>>`, and the extractor stamps `NonNull` as
//!    drop-total (it owns nothing), so the stamp hid the pointee;
//!  * `array::IntoIter` keeps its elements in `[MaybeUninit<T>; N]`, and the wrapper was
//!    accepted without looking inside, though `IntoIter`'s own `Drop` drops them.
//! Review round 73 added three more, also PROVED before:
//!  * `rc_alloc`/`arc_alloc`: `Rc`/`Arc::drop` calls the allocator's `deallocate`,
//!    user code unless the allocator is `Global`, and the walk only checked the
//!    allocator's drop glue;
//!  * `thin_box`: `ThinBox<T>` names `T` only in `PhantomData` behind an opaque header,
//!    so its admitted destructor was credited without the walk ever reaching `T`.
//! Review round 74 found two more sysroot destructors credited although their `Drop`
//! runs code the walk cannot see. Sysroot destructors are now credited only from an
//! audited list:
//!  * `waker`: `Waker::drop` calls a user vtable function (here, via `Arc<impl Wake>`);
//!  * `mpmc_rx`: dropping the last `mpmc::Receiver<T>` drops queued `T`s, behind a
//!    raw-pointer enum the extractor stamps drop-total.
//! Review round 76: `enum_rewrite` is a local enum whose own `Drop` is PROVED panic-free
//! but rewrites the discriminant to a variant holding a `Bomb`. It used to be filed as
//! "no `Drop` impl", so the variant lane trusted the constructed `Safe` tag.
//! `total` holds the same shapes over elements whose drop is total, which must verify
//! (including `array::IntoIter` over `Rc`, whose walk crosses `MaybeDangling`).
#![allow(dead_code)]
#![feature(allocator_api, thin_box, mpmc_channel)]
extern crate dropglue_bomb_dep;
extern crate panicking_allocator_dep;
#[cfg(not(total))]
use dropglue_bomb_dep::Bomb;
use std::rc::Rc;
use std::sync::Arc;

#[cfg(rc)]
pub fn f(x: Rc<Bomb>) {
    drop(x);
}

#[cfg(arc)]
pub fn f(x: Arc<Bomb>) {
    drop(x);
}

#[cfg(opt_rc)]
pub fn f(x: Option<Rc<Bomb>>) {
    drop(x);
}

#[cfg(arr_iter)]
pub fn f(x: core::array::IntoIter<Bomb, 2>) {
    drop(x);
}

#[cfg(local_struct)]
pub struct S {
    r: Rc<Bomb>,
}
#[cfg(local_struct)]
pub fn f(x: S) {
    let _y = x;
}

#[cfg(closure)]
pub fn f(x: Rc<Bomb>) {
    let c = move || {
        let _ = &x;
    };
    let _c = c;
}

#[cfg(rc_alloc)]
pub fn f(x: Rc<u32, panicking_allocator_dep::Q>) {
    drop(x);
}

#[cfg(arc_alloc)]
pub fn f(x: Arc<u64, panicking_allocator_dep::Q>) {
    drop(x);
}

#[cfg(thin_box)]
pub fn f(x: std::boxed::ThinBox<Bomb>) {
    drop(x);
}

#[cfg(waker)]
pub fn f(x: std::task::Waker) {
    drop(x);
}

#[cfg(mpmc_rx)]
pub fn f(x: std::sync::mpmc::Receiver<Bomb>) {
    drop(x);
}

#[cfg(enum_rewrite)]
pub enum E {
    Safe(u32),
    Danger(Bomb),
}
#[cfg(enum_rewrite)]
impl Drop for E {
    fn drop(&mut self) {
        let old = std::mem::replace(self, E::Danger(Bomb(7)));
        std::mem::forget(old);
    }
}
#[cfg(enum_rewrite)]
pub fn f(a: u32) -> u32 {
    let _x = E::Safe(a);
    a / 2
}

#[cfg(total)]
pub fn arr_iter_rc(x: core::array::IntoIter<Rc<u32>, 2>) {
    drop(x);
}
#[cfg(total)]
pub struct T {
    r: Rc<u64>,
}
#[cfg(total)]
pub fn rc(x: Rc<u32>) {
    drop(x);
}
#[cfg(total)]
pub fn arc(x: Arc<String>) {
    drop(x);
}
#[cfg(total)]
pub fn arr_iter(x: core::array::IntoIter<u8, 2>) {
    drop(x);
}
#[cfg(total)]
pub fn local_struct(x: T) {
    let _y = x;
}
