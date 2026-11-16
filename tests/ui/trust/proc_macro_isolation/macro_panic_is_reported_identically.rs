//@ only-apple
//@ proc-macro: forger.rs
//@ revisions: in_process isolated
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//! Trust (D21): a macro's panic is the macro's result. The worker sends the
//! message to rustc, which reports it exactly as it reports an in-process panic,
//! and goes on to expand the next item in the same worker.

extern crate forger;

#[derive(forger::Explode)]
//~^ ERROR proc-macro derive panicked
//~| HELP message: the Explode derive always panics
struct First;

#[derive(forger::Explode)]
//~^ ERROR proc-macro derive panicked
//~| HELP message: the Explode derive always panics
struct Second;

fn main() {}
