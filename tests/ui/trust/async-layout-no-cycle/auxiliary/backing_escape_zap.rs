//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency outside the sysroot whose SAFE functions hold `unsafe` blocks.
//! Its bodies are not in the certifying crate's inventory. Each `poke*` writes a
//! word at a chosen offset into the storage it is handed by a mutable path: a
//! `&mut T`, a `Pin<&mut F>`, a `&mut dyn Any` or a `Pin<&mut dyn Future>` (the
//! last two discard the vtable and write whatever was erased into the `dyn`).
//! `writer` returns a `dyn` closure of its own that writes the `&mut T` it is
//! later called with. `peek` (a shared `&dyn Any`) and `take` (an owned
//! `Box<dyn Any>`) write nothing this crate keeps.

use core::any::Any;
use core::future::Future;
use core::pin::Pin;

pub fn poke<T>(t: &mut T, off: usize, v: usize) {
    unsafe { *((t as *mut T as *mut usize).add(off)) = v }
}

pub fn poke_pin<F: Future>(f: Pin<&mut F>, off: usize, v: usize) {
    unsafe {
        let r = f.get_unchecked_mut();
        *((r as *mut F as *mut usize).add(off)) = v
    }
}

pub fn poke_dyn(d: &mut dyn Any, off: usize, v: usize) {
    unsafe { *((d as *mut dyn Any as *mut usize).add(off)) = v }
}

pub fn poke_dyn_fut(f: Pin<&mut dyn Future<Output = u8>>, off: usize, v: usize) {
    unsafe {
        let r = f.get_unchecked_mut();
        *((r as *mut dyn Future<Output = u8> as *mut usize).add(off)) = v
    }
}

pub fn peek(d: &dyn Any) -> usize {
    core::mem::size_of_val(d)
}

pub fn take(d: Box<dyn Any>) -> usize {
    drop(d);
    1
}

/// A `dyn` closure whose body is this crate's: whoever calls it with a `&mut T`
/// hands that `T` to it through the vtable.
pub fn writer<T>() -> Box<dyn FnMut(&mut T)> {
    Box::new(|t: &mut T| unsafe { *((t as *mut T as *mut usize).add(1)) = 1 << 20 })
}
