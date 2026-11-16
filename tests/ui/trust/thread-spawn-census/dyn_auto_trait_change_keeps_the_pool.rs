//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (P2 review, probes h2, h2c, h12): valid Rust changes a `dyn`
//! value's auto traits with no unsizing coercion. A transmute of
//! `Box<dyn Tr + Send>` to `Box<dyn Tr>`, the job queue's lifetime-erasing
//! transmute of `Box<dyn FnOnce() + 'a>` to `Box<dyn FnOnce() + Send + 'static>`,
//! and a union pun of `&(dyn Tr + Sync)` to `&dyn Tr` keep the vtable, and Miri
//! accepts them (it does not validate a vtable's auto traits). The census keyed
//! principals with their auto traits, so the call through the re-typed value
//! met a pool that could not hold its vtable: `fire`, `work` and `fire_pun` were
//! QUIET, and each really spawned. Principals are now keyed without auto traits
//! (design §5.4 as built): all three are INDIRECT. `quiet` is the same shapes
//! with a spawn-free `launch`: no row.

#![allow(dead_code)]

use std::sync::Mutex;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub trait Tr {
    fn run(&self);
}

pub struct Spawner;
impl Tr for Spawner {
    fn run(&self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
}

pub struct Calm;
impl Tr for Calm {
    fn run(&self) {}
}

pub fn make() -> Box<dyn Tr + Send> { Box::new(Spawner) } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
pub fn make_calm() -> Box<dyn Tr> { Box::new(Calm) }

pub fn fire(b: Box<dyn Tr + Send>) { //[spawning]~ NOTE may spawn (indirect)
    let b: Box<dyn Tr> = unsafe { std::mem::transmute(b) };
    b.run()
}

type Job = Box<dyn FnOnce() + Send + 'static>;
pub static QUEUE: Mutex<Vec<Job>> = Mutex::new(Vec::new());

pub fn submit<'a>(f: Box<dyn FnOnce() + 'a>) {
    let job: Job = unsafe { std::mem::transmute(f) };
    QUEUE.lock().unwrap().push(job);
}

pub fn work() { //[spawning]~ NOTE may spawn (indirect)
    let jobs: Vec<Job> = std::mem::take(&mut *QUEUE.lock().unwrap());
    for job in jobs {
        job();
    }
}

pub fn spawning_job() { submit(Box::new(|| launch())); }

pub union Pun {
    pub a: &'static (dyn Tr + Sync),
    pub b: &'static dyn Tr,
}

static S: Spawner = Spawner;

pub fn mk() -> Pun { Pun { a: &S } }

pub fn fire_pun(p: Pun) { unsafe { p.b.run() } } //[spawning]~ NOTE may spawn (indirect)
