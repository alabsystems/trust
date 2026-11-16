//@ revisions: start assign ref_mut param_store reseat
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
#![allow(unused_variables, unused_mut, unused_assignments, dead_code)]
//! DISC-CSE-PRE-BARRIER-WRITE-1 (docs/KNOWN_HAZARDS.md, docs/DECISION_QUEUE.md): the
//! run witness. Each revision builds ONE function (so one spelling cannot mask
//! another) that reads an enum's discriminant through a shared borrow, changes the
//! enum with a plain statement (or reseats the borrow), and reads it again through a
//! fresh borrow:
//!
//! ```ignore (illustrative)
//! let mut cur = Some(v);
//! if let None = &cur { return 0; }
//! cur = None;
//! if let Some(_) = &cur { 0 } else { v + 255 }
//! ```
//!
//! * `start`       — `self.st = St::Busy` through `&mut self`;
//! * `assign`      — `cur = None`, a whole re-assignment;
//! * `ref_mut`     — `let m = &mut e; *m = None`;
//! * `param_store` — `*e = None` through a `&mut` parameter;
//! * `reseat`      — `r = &b`, a reseat of the shared reference itself.
//!
//! Each is called so the second arm runs: `v + 255` at `v = 1` (`hits + 1` at
//! `hits = 255`) must panic "attempt to add with overflow" exactly as vanilla Rust does.
//!
//! `build_discriminant_cse_facts` grouped the two reads by their canonical referent and
//! tied them (`d1 == d2`) because neither follows a `Call`/`Drop`/`Opaque`, on the claim
//! that only such a barrier can change the referent. The tie made the second arm
//! infeasible, its overflow row was PROVED and kernel-certified, and the advisory lane
//! elided its check (`TRUST_ELIDE: elided 1`).
//!
//! BEFORE (measured 2026-10-12 on the wave-25 probe stage 1, `scratchpad/stage1-w25probe`,
//! each revision built with exactly these flags plus `--cfg <revision>` and
//! `TRUST_ELIDE_DEBUG=1`): every revision built with exit 0 and `TRUST_ELIDE: elided 1
//! kernel-certified overflow checks` for its function, and its binary printed `0` and
//! exited 0; the error pattern never appeared. The same source built
//! `-Ztrust-verify=off`, and by stock `rustc` 1.97.1, panics "attempt to add with
//! overflow" (exit 101) in every revision.
//!
//! AFTER (predicted; FIX PREPARED 2026-10-12, not built on a stage 1): a pre-barrier
//! tie needs a body-stable referent or a frozen shared-reference parameter's pointee.
//! Every referent here is written or reseated, so no tie is made, no row is proved,
//! nothing is elided, and each revision panics with the error pattern. trust-vcgen's
//! `tests/discriminant_cse_statement_write_realmir.rs` measures that row level on the
//! compiler's own extraction of these bodies.

use std::hint::black_box;

#[cfg(start)]
#[derive(Clone, Copy, PartialEq)]
pub enum St {
    Idle,
    Busy,
}

#[cfg(start)]
pub struct Machine {
    pub st: St,
    pub hits: u8,
}

#[cfg(start)]
impl Machine {
    #[inline(never)]
    pub fn start(&mut self) -> u8 {
        if let St::Busy = &self.st {
            return 0;
        }
        self.st = St::Busy;
        match &self.st {
            St::Idle => 0,
            St::Busy => self.hits + 1,
        }
    }
}

#[cfg(assign)]
#[inline(never)]
pub fn assign(v: u8) -> u8 {
    let mut cur = Some(v);
    if let None = &cur {
        return 0;
    }
    cur = None;
    if let Some(_) = &cur { 0 } else { v + 255 }
}

#[cfg(ref_mut)]
#[inline(never)]
pub fn ref_mut(v: u8) -> u8 {
    let mut e: Option<u8> = Some(v);
    let r1 = &e;
    if let None = *r1 {
        return 0;
    }
    let m = &mut e;
    *m = None;
    let r2 = &e;
    match *r2 {
        Some(_) => 0,
        None => v + 255,
    }
}

#[cfg(param_store)]
#[inline(never)]
pub fn param_store(e: &mut Option<u8>, v: u8) -> u8 {
    let r1 = &*e;
    if let None = *r1 {
        return 0;
    }
    *e = None;
    let r2 = &*e;
    match *r2 {
        Some(_) => 0,
        None => v + 255,
    }
}

#[cfg(reseat)]
#[inline(never)]
pub fn reseat(v: u8) -> u8 {
    let a = Some(v);
    let b: Option<u8> = None;
    let mut r = &a;
    if let None = *r {
        return 0;
    }
    r = &b;
    if let Some(_) = *r { 0 } else { v + 255 }
}

fn main() {
    let v = black_box(1u8);
    #[cfg(start)]
    let out = Machine { st: St::Idle, hits: 255 }.start();
    #[cfg(assign)]
    let out = assign(v);
    #[cfg(ref_mut)]
    let out = ref_mut(v);
    #[cfg(param_store)]
    let out = param_store(&mut Some(1), v);
    #[cfg(reseat)]
    let out = reseat(v);
    println!("{out}");
}
