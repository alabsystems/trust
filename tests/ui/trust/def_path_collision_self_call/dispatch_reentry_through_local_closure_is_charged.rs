//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify
//@ compile-flags: --crate-type lib -Ztrust-verify=on
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 7 (2026-10-08) — a dispatched `Fn*` call SERVED BY A LOCAL
//! CLOSURE that calls back is charged on the dispatching body.
//!
//! A closure implements `Fn` / `FnMut` / `FnOnce` by a builtin impl, so round 6's serving
//! set (the trait's provided body and each local impl's item) never held it, and a cycle
//! that leaves through `<dyn Fn as Fn>::call` or `<F as Fn>::call` and comes back through a
//! local closure was charged by nobody:
//!
//! * `dyn_go` calls its own closure through `&dyn Fn` (review scratch
//!   `r11rev/probes/clos_dyn.rs`);
//! * `dynarg_go -> dynarg_apply` (plain) `-> <dyn Fn as Fn>::call -> closure -> dynarg_go`
//!   (`clos_dynarg.rs`);
//! * `struct_go -> W::<C>::run` (plain) `-> <F as Fn>::call -> closure -> struct_go`
//!   (`clos_struct.rs`);
//! * `mut_go` calls its own closure through `&mut dyn FnMut` (scratch `r12/probes/
//!   clos_mut_dyn.rs`).
//!
//! The closure passed DIRECTLY as a call argument (`apply(&|m| go(m), n)` with a generic
//! `apply`) was already an SCC edge and is not pinned here. MEASURED (level 2, JSON, the
//! probes as separate crates): no termination row for the first three shapes on preview3
//! (`7be75e9a80`), round 5 and round 6, and for the fourth on round 5; round 7 charges one D9
//! dispatch row on each dispatching body (`dyn_go`, `dynarg_apply`, `W::run`, `mut_go`). Every
//! shape also fails the default lane for reasons unrelated to termination (unproved
//! Level-0/strict rows of the closures and `dyn` calls), so this file is `check-fail` on
//! both revisions and pins only the termination diagnostics.

pub fn dyn_go(n: u64) -> u64 {
    //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
    //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
    if n == 0 {
        return 0;
    }
    let f: &dyn Fn(u64) -> u64 = &|m: u64| dyn_go(m);
    f(n)
}

fn dynarg_apply(f: &dyn Fn(u64) -> u64, n: u64) -> u64 {
    //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
    //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
    f(n)
}

pub fn dynarg_go(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    dynarg_apply(&|m: u64| dynarg_go(m), n)
}

struct W<F>(F);

impl<F: Fn(u64) -> u64> W<F> {
    fn run(&self, n: u64) -> u64 {
        //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
        //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
        (self.0)(n)
    }
}

pub fn struct_go(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    W(|m: u64| struct_go(m)).run(n)
}

pub fn mut_go(n: u64) -> u64 {
    //[default]~^ WARN termination is ASSUMED, not proved — 1 dispatched call(s) reach a trait method
    //[certify]~^^ ERROR termination is not established — 1 dispatched call(s) reach a trait method
    if n == 0 {
        return 0;
    }
    let f: &mut dyn FnMut(u64) -> u64 = &mut |m: u64| mut_go(m);
    f(n)
}
