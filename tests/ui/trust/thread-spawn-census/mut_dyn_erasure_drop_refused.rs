//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a value erased to `dyn` through `&mut` is a drop
//! observation. The census used to skip every reference-sourced erasure on the
//! claim that "a shared or mutable reference to a trait object never drops its
//! pointee". Unsafe code can: `ptr::drop_in_place(r as *mut dyn Any)` runs the
//! erased type's drop glue, and the body that does it sees only `dyn Any`.
//! `drop_through_mut_dyn` carried no spawn row while the same drop without
//! `dyn` (`drop_in_place(s as *mut Spawner)`) was refused (review probe n3.rs,
//! 2026-09-29). Since P2 (design 2026-09-29-spawn-census-by-construction §5.4)
//! the vtable's drop slot joins the `dyn Any` drop pool at every erasure, and
//! it is a CREATE (an ESCAPES row) at the erasure only when the innermost
//! pointer is not a shared `&`; the drop through the trait object is INDIRECT
//! where it happens. `drop_through_raw` is S2 through
//! `drop_in_place::<Spawner>`. A `&` erasure (`erase_interior_mutable`) is no
//! row: nothing is dropped through `&dyn Any` without UB, and code that
//! downcasts it back and replaces the cell's contents
//! (`Cell::<Option<Spawner>>::set`) holds the concrete type and is refused
//! there (W11 refused the erasure itself as an UNKNOWN). `quiet` is the same
//! shapes with a spawn-free `launch`: no row.

#![allow(dead_code)]

use std::any::Any;
use std::cell::Cell;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub struct Spawner;

impl Drop for Spawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch()
    }
}

pub fn drop_through_mut_dyn(s: &mut Spawner) { //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    //[spawning]~^ NOTE may spawn (indirect): an indirect call
    let r: &mut dyn Any = s;
    let p = r as *mut dyn Any;
    // SAFETY: test shape only; never executed.
    unsafe { std::ptr::drop_in_place(p) }
}

// The same drop without `dyn`: the raw pointer is handed to an external callee.
pub fn drop_through_raw(s: &mut Spawner) { //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::ptr::drop_in_place::<Spawner>
    let p = s as *mut Spawner;
    // SAFETY: test shape only; never executed.
    unsafe { std::ptr::drop_in_place(p) }
}

pub fn erase_interior_mutable(c: &'static Cell<Option<Spawner>>) -> &'static dyn Any { c }

pub fn replace_through_downcast(c: &dyn Any) { //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::cell::Cell::<std::option::Option<Spawner>>::set
    if let Some(cell) = c.downcast_ref::<Cell<Option<Spawner>>>() {
        cell.set(None);
    }
}
