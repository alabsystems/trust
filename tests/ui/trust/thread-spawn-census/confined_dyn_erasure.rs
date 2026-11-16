//@ revisions: once map stashed guard
//@[stashed] aux-build:registry_dep.rs
//@[guard] aux-build:guard_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[once] forbid-output:may spawn (indirect)
//@[map] forbid-output:may spawn (indirect)
//! Spawn census (design §5.4 confinement; P2m cost 3): a `dyn` value that
//! erases a reference to a local of its frame can be called only while that
//! frame is live, by code it runs, unless unsafe code extends the reference's
//! lifetime. Its vtable is CONFINED: an invoke in external code does not see
//! it, and its creator, and every local frame that hands it to external code
//! (a call, an indirect call, a drop), is charged instead.
//!
//! * `once`: std's `OnceLock::get_or_init` erases each initializer as a
//!   `&mut dyn FnMut(&OnceState)` of a local of `Once::call_once_force`, and
//!   `Once::call` invokes it. A spawning initializer used to make every other
//!   `get_or_init` INDIRECT (aterm-ctl: 564 functions); `name` is QUIET, and
//!   `start` stays refused through the creator it calls.
//! * `map`: std's hashbrown erases each map's rehash hasher as a `&dyn Fn` of
//!   a local of `reserve_rehash`; a key type whose `Hash` spawns no longer
//!   reaches `quiet`'s insert.
//! * `stashed` (refused): a transmute extends the reference to `'static`, a
//!   registry keeps it, and a call that hands it nothing runs it while the
//!   closure is live: the transmute demotes it, so `fire` is INDIRECT.
//! * `guard` (refused): an external guard's `Drop` calls the borrowed
//!   callback; `consume` drops it, and is charged as at a call.

#![allow(dead_code)]

#[cfg(once)]
mod once {
    use std::sync::OnceLock;

    static CONNECTOR: OnceLock<u32> = OnceLock::new();
    static NAME: OnceLock<u32> = OnceLock::new();

    pub fn start() -> u32 {
        //[once]~^ NOTE callee names, erases or reads a callable that reaches a std thread spawn
        *CONNECTOR.get_or_init(|| {
            let _handle = std::thread::spawn(|| {});
            1
        })
    }

    pub fn name() -> u32 { *NAME.get_or_init(|| 5) }
}

#[cfg(map)]
mod map {
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};

    #[derive(PartialEq, Eq)]
    pub struct Loud(pub u32);

    impl Hash for Loud {
        fn hash<H: Hasher>(&self, state: &mut H) {
            let _handle = std::thread::spawn(|| {});
            self.0.hash(state);
        }
    }

    pub fn loud(m: &mut HashMap<Loud, u32>) { m.insert(Loud(1), 1); } //[map]~ NOTE reaches a std thread spawn

    pub fn quiet(m: &mut HashMap<u32, u32>) { m.insert(1, 1); }
}

#[cfg(stashed)]
extern crate registry_dep;

#[cfg(stashed)]
pub fn stash() {
    //[stashed]~^ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    let mut c = || {
        let _handle = std::thread::spawn(|| {});
    };
    let r: &mut dyn FnMut() = &mut c;
    registry_dep::register(unsafe {
        std::mem::transmute::<&mut dyn FnMut(), &'static mut dyn FnMut()>(r)
    });
    // While `c` is live: the registry runs it from a call that hands it nothing.
    fire();
}

#[cfg(stashed)]
pub fn fire() { registry_dep::fire_registered() } //[stashed]~ NOTE may spawn (indirect)

#[cfg(guard)]
extern crate guard_dep;

#[cfg(guard)]
pub fn guarded() {
    //[guard]~^ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
    let mut c = || {
        let _handle = std::thread::spawn(|| {});
    };
    consume(guard_dep::OnDrop(&mut c));
}

#[cfg(guard)]
fn consume(_g: guard_dep::OnDrop<'_>) {} //[guard]~ NOTE may spawn (indirect)
