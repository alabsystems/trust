//@ revisions: absent control
//@ needs-trust-verify
//@ aux-build: typed_handle_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[absent] forbid-output: value dropped here has drop glue that may run a local Drop impl
//@[absent] forbid-output: caller effect is unmodeled
//! W11 spawn census, final verification (2026-09-30): a SPAWN claim at a drop
//! (S3) needs glue that really runs the spawning `Drop`. A type that needs no
//! drop runs no glue, wherever it sits: `PhantomData<Job>`, `[Job; 0]`, a
//! dependency's typed `Id<Job>`. Each of the `absent` shapes below was a spawn
//! claim ("value dropped here has drop glue that may run a local Drop impl"),
//! and its caller was told its callee "transitively spawns", because the walk
//! read every `PhantomData<T>` inside an external type as a certain drop of a
//! `T` — including `Vec<PhantomData<Job>>` (the declared `T` is itself a
//! no-drop `PhantomData`), `Result<PhantomData<Job>, String>` (a std type
//! without a `Drop` impl declares nothing), and a dependency's `Handle<T>`
//! whose `Drop` impl never touches a `T`. None drops a `Job`; each is at most
//! an unknown now. `control` keeps the claims whose glue does drop a `Job`.

#![allow(dead_code)]

extern crate typed_handle_dep;

pub struct Job(u8);
impl Drop for Job {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}

#[cfg(absent)]
mod absent {
    use super::Job;
    use std::marker::PhantomData;
    use std::rc::Rc;
    use std::sync::Mutex;
    use typed_handle_dep::{Handle, Holder, Id};

    pub fn vec_phantom(_v: Vec<PhantomData<Job>>) {}
    pub fn box_zero(_b: Box<[Job; 0]>) {}
    pub fn result_phantom(_r: Result<PhantomData<Job>, String>) {}
    pub fn opt_tuple_zero(_o: Option<([Job; 0], String)>) {}
    pub fn rc_tuple_phantom(_r: Rc<(PhantomData<Job>, String)>) {}
    pub fn mutex_zero(_m: Mutex<[Job; 0]>) {}
    pub fn opt_vec_phantom(_o: Option<Vec<PhantomData<Job>>>) {}
    pub fn dep_handle(_h: Handle<Job>) {}
    pub fn dep_holder(_h: Holder<Job>) {}
    pub fn vec_dep_id(_v: Vec<Id<Job>>) {}
    const EMPTY: Vec<PhantomData<Job>> = Vec::new();
    pub fn const_empty() {
        let _v = EMPTY;
    }
    pub fn caller(v: Vec<PhantomData<Job>>) {
        vec_phantom(v)
    }
}

#[cfg(control)]
mod control {
    use super::Job;
    use std::marker::PhantomData;
    use typed_handle_dep::Pair;

    pub fn vec_tuple(_v: Vec<(PhantomData<u8>, Job)>) {} //[control]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn result_job(_r: Result<Job, String>) {} //[control]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn box_array(_b: Box<[Job; 2]>) {} //[control]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn dep_pair(_p: Pair<Job>) {} //[control]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn caller(b: Box<[Job; 2]>) { box_array(b) } //[control]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}
