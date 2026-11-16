//@ revisions: certain uncertain open
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[uncertain] forbid-output: a std thread spawn through calls and drops; caller
//@[uncertain] forbid-output: value dropped here
//@[uncertain] forbid-output: not a spawn claim
//@[open] forbid-output: a std thread spawn through calls and drops; caller
//@[open] forbid-output: value dropped here
//! Spawn census: a spawn CLAIM needs a path to the spawning `Drop` that the
//! census walked; what it cannot see is an UNKNOWN, never a claim.
//!
//! `certain`: what an external type OWNS. Its glue drops the `Job`, so
//! dropping one (a MIR `Drop`, S3) is a spawn claim ("may run"): `Box`, `Vec`,
//! `Option`, `Rc`, `Arc`, `HashMap`, `Mutex`, a `JoinHandle`'s result slot,
//! and (since P2, design 2026-09-29-spawn-census-by-construction) a
//! `Sender<Job>`, whose last drop frees the channel and the messages still in
//! it. A callee that drops one is walked too: `v.clear()` is S2 through
//! `Vec::<Job>::clear` (W11: an UNKNOWN hand-off).
//!
//! `uncertain`: what W11 could reach only through an external type's opaque
//! glue or through `&` — a `MutexGuard<Job>` holds a `&Mutex<Job>`, a
//! `Ref<Job>` a pointer into the `RefCell`, a `Weak<Job>` a pointer to a value
//! it never drops. W11 refused each as an UNKNOWN; until the W11 landing review
//! (2026-09-29) each was a spawn claim. Since P2 the census walks those drops
//! and finds no `Job` dropped, so none of them carries a row.
//!
//! `open`: `h_pin_future` names `dyn Future<Output = Job>`, a principal no code
//! the census walked erases a value to. Its pool is open (design §5.4, the
//! trust-mc rule), so EVERY pool is unclosed and every function that reaches
//! an indirect call (std's panic and formatting paths included) is UNKNOWN
//! ("not enumerated (no spawn was found)"): refused, never a spawn claim.

#![allow(dead_code)]

pub struct Job(u8);
impl Drop for Job {
    fn drop(&mut self) { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
        let _h = std::thread::spawn(|| {});
    }
}

#[cfg(certain)]
mod certain {
    use super::Job;
    use std::collections::HashMap;
    use std::rc::Rc;
    use std::sync::{Arc, Mutex};

    pub fn d_box(_b: Box<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_vec(_v: Vec<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_opt(_o: Option<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_rc(_r: Rc<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_arc(_a: Arc<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_map(_m: HashMap<u8, Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_mutex(_m: Mutex<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn d_join(_h: std::thread::JoinHandle<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn h_vec_clear(v: &mut Vec<Job>) { v.clear() } //[certain]~ NOTE callee reaches a std thread spawn through calls and drops; caller effect is unmodeled (via std::vec::Vec::<Job>::clear
    pub fn d_sender(_s: std::sync::mpsc::Sender<Job>) {} //[certain]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
    pub fn c_box(b: Box<Job>) { d_box(b) } //[certain]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

#[cfg(uncertain)]
mod uncertain {
    use super::Job;
    use std::cell::{Ref, RefCell};
    use std::sync::{Mutex, MutexGuard};

    pub fn d_guard(_g: MutexGuard<'_, Job>) {}
    pub fn d_ref(_r: Ref<'_, Job>) {}
    pub fn d_weak(_w: std::rc::Weak<Job>) {}
    pub fn h_drop_guard(m: &Mutex<Job>) { drop(m.lock()) }
    pub fn h_borrow(c: &RefCell<Job>) -> u8 { c.borrow().0 }
    pub fn c_guard(m: &Mutex<Job>) { h_drop_guard(m) }
}

#[cfg(open)]
mod open {
    use super::Job;
    use std::sync::{Mutex, MutexGuard};

    pub fn h_pin_future(f: &std::pin::Pin<Box<dyn std::future::Future<Output = Job>>>) -> usize {
        std::mem::size_of_val(f)
    }
    pub fn d_guard(_g: MutexGuard<'_, Job>) {} //[open]~ NOTE not enumerated (no spawn was found)
    pub fn h_drop_guard(m: &Mutex<Job>) { drop(m.lock()) } //[open]~ NOTE not enumerated (no spawn was found)
    pub fn c_guard(m: &Mutex<Job>) { h_drop_guard(m) } //[open]~ NOTE not enumerated (no spawn was found)
}
