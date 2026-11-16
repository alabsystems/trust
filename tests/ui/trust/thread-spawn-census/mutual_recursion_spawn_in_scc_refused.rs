//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! W11 transitive spawn census over a mutual-recursion SCC. The census is a
//! backward fixpoint over the same pre-steal local call graph the SCC oracle
//! uses, so a cycle neither loops nor withholds a body: in `spawning`, the spawn
//! in `ping` reaches `pong` (through the cycle edge) and `enters_scc` (through
//! `pong`), and `ping` itself carries both the direct row and the transitive row
//! for its call to `pong`. In `quiet` the same cycle never spawns and no spawn
//! row may appear. (Both revisions fail on the cycle's missing `decreases`
//! measure — a termination row unrelated to this census.)

#![allow(dead_code)]

#[cfg(spawning)]
pub fn ping(n: u8) {
    //[spawning]~^ NOTE direct std thread spawn lacks an authenticated execution and race model
    //[spawning]~| NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    if n == 0 {
        let _handle = std::thread::spawn(|| {});
    } else {
        pong(n - 1);
    }
}

#[cfg(quiet)]
pub fn ping(n: u8) {
    if n > 0 {
        pong(n - 1);
    }
}

pub fn pong(n: u8) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    ping(n);
}

pub fn enters_scc() { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
    pong(3);
}
