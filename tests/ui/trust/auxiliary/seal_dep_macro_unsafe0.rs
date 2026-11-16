//@ edition: 2021
//@ compile-flags: --crate-type=rlib -Copt-level=0 -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_macro_unsafe.rs` and its `_holds`
//! twin, built without optimization: fns whose author wrote no `unsafe`, some of which
//! hold std's `pin!` or a `thread_local!` declared inside them (each writes
//! an `unsafe` block of its own into the fn), and one, `pin_raw`, whose
//! author did. Sound.
pub trait Make { type Out; }

// ---- must HOLD, and do (controls)
pub fn pin_only<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let p = ::core::pin::pin!(a);
    let pa: *const M::Out = &**p.as_ref().get_ref();
    let pb: *const M::Out = b;
    pa == pb
}
pub fn print_only<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    eprintln!("print_only: same={}", pa == pb);
    pa == pb
}
fn pin_helper<M: Make>(a: &mut M::Out) -> *const M::Out { let p = ::core::pin::pin!(a); &**p.as_ref().get_ref() }
pub fn pin_elsewhere_print<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa = pin_helper::<M>(a);
    let pb: *const M::Out = b;
    eprintln!("pin_elsewhere_print: same={}", pa == pb);
    pa == pb
}
pub async fn plain_async<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa: *const M::Out = a; let pb: *const M::Out = b;
    async { 1u8 }.await == 1 && pa == pb
}
pub fn tl_inner_quiet<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    thread_local! { static IN: ::core::cell::Cell<u32> = const { ::core::cell::Cell::new(0) }; }
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    IN.with(|c| c.set(c.get() + 1));
    pa == pb
}

// ---- must HOLD per the doc, REFUSED: pin!/thread_local! in the same fn
// as compiler-lowered safe code.
pub fn pin_print<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let p = ::core::pin::pin!(a);
    let pa: *const M::Out = &**p.as_ref().get_ref();
    let pb: *const M::Out = b;
    eprintln!("pin_print: same={}", pa == pb);
    pa == pb
}
pub fn pin_unbox<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let p = ::core::pin::pin!(a);
    let pa: *const M::Out = &**p.as_ref().get_ref();
    let pb: *const M::Out = b;
    let bx = Box::new(pa == pb);
    *bx
}
pub async fn pin_async<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let pa: *const M::Out = a; let pb: *const M::Out = b;
    let inner = ::core::pin::pin!(async { 1u8 });
    inner.await == 1 && pa == pb
}
pub fn pin_closure_print<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let f = |a: &mut M::Out| { let p = ::core::pin::pin!(a); let q: *const M::Out = &**p.as_ref().get_ref(); q };
    let pa = f(a);
    let pb: *const M::Out = b;
    eprintln!("pin_closure_print: same={}", pa == pb);
    pa == pb
}
pub fn tl_inner<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    thread_local! { static IN: ::core::cell::Cell<u32> = const { ::core::cell::Cell::new(0) }; }
    let pa: *mut M::Out = a; let pb: *mut M::Out = b;
    IN.with(|c| c.set(c.get() + 1));
    eprintln!("tl_inner: {}", IN.with(|c| c.get()));
    pa == pb
}

// ---- must FAIL: the author's own `unsafe`, in a fn that also holds `pin!`.
pub fn pin_raw<M: Make>(a: &mut M::Out, b: &mut M::Out) -> bool {
    let p = ::core::pin::pin!(a);
    let pa: *const M::Out = &**p.as_ref().get_ref();
    let pb: *const M::Out = b;
    eprintln!("pin_raw: same={}", pa == pb);
    let _ = unsafe { ::core::ptr::read(pb as *const u8) };
    pa == pb
}
