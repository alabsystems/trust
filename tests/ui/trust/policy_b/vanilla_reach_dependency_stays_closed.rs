//@ needs-trust-verify
//@ aux-build: vanilla_reach_dep.rs
//@ revisions: dep_elem dep_elem_strict ioerror_drop ioerror_drop_strict ioerror_question
//@ revisions: ioerror_kind
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@[dep_elem_strict] compile-flags: -Ztrust-policy=strict
//@[ioerror_drop_strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The dependency halves of `vanilla_reach_local_plain_data.rs` and
//! `ioerror_payload_closed_graph.rs` (VANILLA-REACH-1 and IOERROR-PAYLOAD-1,
//! docs/DECISION_QUEUE.md). Each body here is one the no-dependency fixtures
//! admit; with a verify-off dependency in the crate graph each stays refused.
//!
//!  * `dep_elem`: `Vec::<(u32, Option<dep::Plain>)>::push`. A dependency's ADT is
//!    not plain data, however plain it looks: its impls are unverified code.
//!  * `ioerror_*`: an `io::Error` may now carry a dependency's payload
//!    (`dep::bomb_error(7)` makes one whose destructor panics), so its
//!    `Box<dyn Error>` reaches unverified code and every walk that meets it opens,
//!    as before IOERROR-PAYLOAD-1. The bodies below never call `dep`: the rule is
//!    a fact about the crate GRAPH, because the value a body is handed may come
//!    from anywhere in it.
extern crate vanilla_reach_dep as dep;

use std::io::Write;
use std::path::Path;

#[cfg(any(dep_elem, dep_elem_strict))]
pub fn push(v: &mut Vec<(u32, Option<dep::Plain>)>, x: u32) {
    //[dep_elem,dep_elem_strict]~^ ERROR Trust
    v.push((x, None));
}

#[cfg(any(ioerror_drop, ioerror_drop_strict, ioerror_question))]
pub fn append(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    //[ioerror_question]~^ ERROR Trust
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path)?;
    f.write_all(bytes)
}

#[cfg(any(ioerror_drop, ioerror_drop_strict))]
pub fn consume(e: std::io::Error) -> u32 {
    //[ioerror_drop,ioerror_drop_strict]~^ ERROR Trust
    let _ = e;
    1
}

#[cfg(ioerror_kind)]
pub fn kind(e: &std::io::Error) -> std::io::ErrorKind {
    //[ioerror_kind]~^ ERROR Trust
    e.kind()
}
