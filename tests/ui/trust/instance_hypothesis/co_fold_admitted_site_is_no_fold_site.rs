//~ NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":3,"runtime_checked":1,"cached":0,"total":4}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-pass
//@[certify] check-fail
//! OD-1 phase 1: the phase-0 co-fold shape (`co_fold_open_dispatch_stays_failed.rs`)
//! with an ADMITTED open dispatch. The admitted site is no fold site (no `Assert(false)`,
//! no `PanicFreedom` obligation), so the whole-function aggregate stands for the concrete
//! `Vec::<u32>::push` alone and keeps its own label, `runtime_checked` (as
//! `co_fold_concrete_only_control.rs`), and the open dispatch publishes its own
//! `assumption:instance-hypothesis` row (line 1: one runtime-checked row, three skipped
//! — the hypothesis, the inventory row, the global-alloc row — nothing failed). The
//! refutation of a NON-admitted co-folded site is unchanged: see the raw-pointer
//! fixtures. Strict passes CONDITIONALLY (the vanilla sysroot callee's runtime-checked
//! row is tolerated there, as without the open call); certify refuses.
pub trait Tr {
    fn m(&self) -> u32;
}

pub fn concrete_first<T: Tr>(v: &mut Vec<u32>, t: &T) -> u32 {
    //[certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~^^ ERROR Trust strict verification failed
    //[certify]~^^^ ERROR Trust certify verification failed for `co_fold_admitted_site_is_no_fold_site::concrete_first`: 1 instance hypothesis row(s)
    v.push(1);
    t.m()
}
