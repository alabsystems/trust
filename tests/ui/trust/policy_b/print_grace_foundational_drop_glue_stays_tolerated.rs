//@ revisions: default strict memory_safe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type=lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! The controls for `print_grace_drop_glue_reaches_foreign_code.rs`: the print
//! grace still covers a body whose only other drop glue is foundational code at
//! foundational types — `drop_ty_has_masked_fail_closed_glue` now asks what a
//! foundational destructor's WHOLE type reaches (`foundational_destructor_foreign_reach`),
//! and for these it reaches nothing outside the sysroot. A `&dyn` borrow is not
//! dropped at all, and a `BufWriter` over a `Vec<u8>` flushes through std's own
//! `Write`. Each builds rc=0 under the default policy, strict and memory-safe on
//! stage-1 `f2e5ebbc0f` and with the change.
use std::any::Any;
use std::collections::HashMap;
use std::io::BufWriter;
use std::rc::Rc;

pub fn print_only(x: u32) {
    println!("{}", x);
}

pub fn string(s: String, x: u32) {
    println!("{}", x);
    let _s = s;
}

pub fn vec_of_u32(v: Vec<u32>, x: u32) {
    println!("{}", x);
    let _v = v;
}

pub fn box_of_u32(b: Box<u32>, x: u32) {
    println!("{}", x);
    let _b = b;
}

pub fn bufwriter_of_vec(w: BufWriter<Vec<u8>>, x: u32) {
    println!("{}", x);
    let _w = w;
}

pub fn hash_map(m: HashMap<u32, u32>, x: u32) {
    println!("{}", x);
    let _m = m;
}

pub fn rc_of_u32(r: Rc<u32>, x: u32) {
    println!("{}", x);
    let _r = r;
}

pub fn option_of_string(s: Option<String>, x: u32) {
    println!("{}", x);
    let _s = s;
}

pub fn tuple(t: (String, Vec<u8>), x: u32) {
    println!("{}", x);
    let _t = t;
}

pub fn closure_captures_string(s: String, x: u32) {
    println!("{}", x);
    let _c = move || {
        let _r = &s;
    };
}

pub struct Local {
    pub a: u32,
    pub s: String,
}

pub fn local_struct(l: Local, x: u32) {
    println!("{}", x);
    let _l = l;
}

/// A trait object behind a borrow: nothing here drops it.
pub fn dyn_reference(r: &dyn Any, s: String, x: u32) {
    println!("{}", x);
    let _s = s;
    let _r = r;
}
