//@ revisions: default strict memory_safe
//@ needs-trust-verify
//@ aux-build: print_grace_writer_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type=lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! The print grace covers std's print backend ALONE (Option Y): a fail-closed panic
//! source folded into the same whole-function panic-freedom aggregate — a dependency
//! call, a sysroot routine at a dependency type, foreign DROP GLUE — withholds it.
//! The drop half of that rule is `drop_ty_has_masked_fail_closed_glue`, and it saw
//! only `Drop` impls outside the TCB. A foundational destructor ended the question
//! ("panic-free by TCB"), so the code the dropped VALUE chose was never asked about:
//! a trait object's glue (`Box<dyn Any>`'s content, `Rc<dyn Any>`'s pointee), the
//! `W::write` a `BufWriter<W>` flushes through, the vtable a `Waker` carries, the
//! boxed `dyn Error` inside an `io::Error`. A trait object named no `Drop` for the
//! scan to judge, so it answered "not masked" — against its own doc ("unresolved
//! droppy shapes resolve to `true`").
//!
//! MEASURED on stage-1 `f2e5ebbc0f` (the r13 refix's left-open and the r14 review's
//! P2): every function below built rc=0 under the default policy, strict AND
//! memory-safe (`no_print_vanilla_gap` under default and strict; memory-safe refused
//! it already), while the same bodies without the `println!` were refused. A
//! verify-off `main` handing the `Box<dyn Any>`, `BufWriter<&mut dyn Write>`, local
//! `Holder`, `io::Error` and `Waker` shapes a value whose destructor, vtable `drop` or
//! `write` stores through a null pointer died with SIGSEGV (rc=139). `certify`
//! refused every one (it tolerates no print gap) and is not a revision here.
//!
//! Now a foundational destructor is TCB only when its whole type reaches no foreign
//! user code (`foundational_destructor_foreign_reach`, the rule the memory-safe skip
//! edges share), and a droppy shape the component walk cannot enumerate (a trait
//! object, a type parameter, an alias, a coroutine) is masked. The controls that
//! keep the grace are `print_grace_foundational_drop_glue_stays_tolerated.rs`.
//!
//! The spawn census (design 2026-09-29-spawn-census-by-construction P2) refused
//! each function here too, until its review: a trait object no code the census
//! walks minted was an open principal. Principal keys no longer include auto
//! traits, so `dyn Any` shares its pools with the panic payload's
//! `dyn Any + Send`, whose vtables std mints; nothing here starts a thread, and
//! the census adds no row. The second half of this file (writers behind
//! `&mut dyn Write`, dependency writers, `io::Error`, `Waker`, and the no-print
//! control) is `print_grace_drop_glue_reaches_foreign_code_writers.rs`, split
//! off when the census's rows made the output exceed what compiletest captures.
extern crate print_grace_writer_dep as dep;

use std::any::Any;
use std::io::{BufWriter, LineWriter, Write};

pub fn box_dyn(b: Box<dyn Any>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::box_dyn`
    println!("{}", x);
    let _b = b;
}

pub fn rc_dyn(b: std::rc::Rc<dyn Any>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::rc_dyn`
    println!("{}", x);
    let _b = b;
}

pub fn arc_dyn(b: std::sync::Arc<dyn Any + Send + Sync>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::arc_dyn`
    println!("{}", x);
    let _b = b;
}

pub fn vec_of_box_dyn(b: Vec<Box<dyn Any>>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::vec_of_box_dyn`
    println!("{}", x);
    let _b = b;
}

pub fn option_of_box_dyn(b: Option<Box<dyn Any>>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::option_of_box_dyn`
    println!("{}", x);
    let _b = b;
}

pub fn box_dyn_fn(b: Box<dyn Fn()>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::box_dyn_fn`
    println!("{}", x);
    let _b = b;
}

pub fn box_dyn_write(b: Box<dyn Write>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::box_dyn_write`
    println!("{}", x);
    let _b = b;
}

/// The drop-and-replace of `*r` drops the old box in this body.
pub fn replace_through_reference(r: &mut Box<dyn Any>, n: Box<dyn Any>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::replace_through_reference`
    println!("{}", x);
    *r = n;
}

pub fn closure_captures_box_dyn(b: Box<dyn Any>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::closure_captures_box_dyn`
    println!("{}", x);
    let _c = move || {
        let _r = &b;
    };
}

pub fn bufwriter_of_box_dyn(w: BufWriter<Box<dyn Write>>, x: u32) {
    //~^ ERROR verification failed for `print_grace_drop_glue_reaches_foreign_code::bufwriter_of_box_dyn`
    println!("{}", x);
    let _w = w;
}
