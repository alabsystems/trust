//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! W11 transitive spawn census: a std thread spawn hidden behind local,
//! statically resolved wrappers keeps its `UnmodeledThreadSpawnEffect` refusal
//! at EVERY caller on the path, not only at the wrapper's direct caller.
//!
//! The one-hop census this replaced refused `one_hop` (its callee spawns
//! directly) but let `two_hop` and `three_hop` through with no row for the
//! spawn at all. Each caller below must carry the transitive refusal row; the
//! spawner itself carries the direct one. The row is a refusal only — an absent
//! row is not race-freedom evidence (see `quiet`, which is simply not observed).

#![allow(dead_code)]

pub fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

pub fn one_hop() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    launch();
}

pub fn two_hop() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    one_hop();
}

pub fn three_hop() { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    two_hop();
}

// A spawn behind a local impl of a FOREIGN trait: the syntactic callee is
// `core::default::Default::default`; only the resolved instance is local.
pub struct Spawner;
impl Default for Spawner {
    fn default() -> Self { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch();
        Spawner
    }
}
pub fn via_foreign_trait_impl() -> Spawner { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    Spawner::default()
}

pub fn quiet(x: u8) -> u8 {
    x / 2
}
