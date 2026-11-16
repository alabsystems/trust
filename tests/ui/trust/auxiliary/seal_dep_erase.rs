//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_dyn_inputs.rs` and `_dyn_inputs_holds.rs`:
//! Safe and sound; forbids unsafe. `any_handler` RUNS nothing: it returns a
//! `fn(&mut dyn Any, &mut dyn Any)`. The handed-out `swap_any::<P>`
//! downcasts each `dyn Any` back to the pointer type `P` and swaps what the
//! two pointers point to. What the caller passes the pointer is the caller's.
#![forbid(unsafe_code)]
use std::any::Any;
use std::ops::DerefMut;

pub fn any_handler<P: 'static + DerefMut>() -> fn(&mut dyn Any, &mut dyn Any)
where
    P::Target: Sized,
{
    swap_any::<P>
}
fn swap_any<P: 'static + DerefMut>(a: &mut dyn Any, b: &mut dyn Any)
where
    P::Target: Sized,
{
    if let (Some(a), Some(b)) = (a.downcast_mut::<P>(), b.downcast_mut::<P>()) {
        std::mem::swap(&mut **a, &mut **b)
    }
}

/// Twin: the handed-out fn's inputs SAY what they point to (`&mut P`), so
/// the swap of `P::Target` is visible where the pointer is made.
pub fn plain_handler<P: DerefMut>() -> fn(&mut P, &mut P)
where
    P::Target: Sized,
{
    swap_plain::<P>
}
fn swap_plain<P: DerefMut>(a: &mut P, b: &mut P)
where
    P::Target: Sized,
{
    std::mem::swap(&mut **a, &mut **b)
}

/// A BOXED `dyn Fn` whose inputs are `&mut dyn Any` (the vtable path).
pub fn boxed_any<P: 'static + DerefMut>() -> Box<dyn Fn(&mut dyn Any, &mut dyn Any)>
where
    P::Target: Sized,
{
    Box::new(|a: &mut dyn Any, b: &mut dyn Any| {
        if let (Some(a), Some(b)) = (a.downcast_mut::<P>(), b.downcast_mut::<P>()) {
            std::mem::swap(&mut **a, &mut **b)
        }
    })
}

/// The same body, called DIRECTLY (not handed out as a value).
pub fn swap_any_direct<P: 'static + DerefMut>(a: &mut dyn Any, b: &mut dyn Any)
where
    P::Target: Sized,
{
    swap_any::<P>(a, b)
}

/// A pub direct entry to the same swap, for the control.
pub fn swap_any_pub<P: 'static + DerefMut>(a: &mut dyn Any, b: &mut dyn Any)
where
    P::Target: Sized,
{
    swap_any::<P>(a, b)
}
